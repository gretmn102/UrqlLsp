module Qsp.Parser.Main
open FParsec
open FsharpMyExtension
open FsharpMyExtension.Either
open Qsp

open Qsp.Ast
open Qsp.Parser.Generic
open Qsp.Parser.Expr

let applyLoc (r, locName) =
    let locNameLower = String.toLower locName
    appendToken2 Tokens.TokenType.NameLabel r
    >>. appendLocHighlight r locNameLower VarHighlightKind.ReadAccess
    >>. pGetDefLocPos locNameLower
        >>= function
            | None ->
                updateUserState (fun st ->
                    { st with
                        NotDefinedLocs =
                            st.NotDefinedLocs
                            |> Map.addOrMod locNameLower [r] (fun xs -> r::xs)
                    }
                )
            | Some _ -> preturn ()

let ppunctuationTerminator : _ Parser =
    appendToken Tokens.TokenType.PunctuationTerminatorStatement (pchar '&')

let pImplicitVarWhenAssign p =
    applyRange p
    >>= fun (range, (name:string)) ->
        let nameLower = name.ToLower()
        Defines.vars
        |> Map.tryFind nameLower
        |> function
            | Some dscr ->
                appendHover2 (RawDescription dscr) range
            | None ->
                if Map.containsKey nameLower Defines.procs then
                    appendSemanticError range "Нельзя переопределять процедуру"
                elif Map.containsKey nameLower Defines.functionsByName then
                    appendSemanticError range "Нельзя переопределять функцию"
                else
                    let dscr = "Пользовательская глобальная переменная числового типа"
                    appendHover2 (RawDescription dscr) range
        >>. appendToken2 Tokens.TokenType.Variable range
        >>. appendVarHighlight range name VarHighlightKind.WriteAccess
        >>. preturn name

let pAssign stmts =
    let assdef name =
        let str_ws s =
            appendToken Tokens.TokenType.OperatorAssignment
                (pstring s)
            .>> ws

        choice [
            str_ws "-=" >>. pexpr |>> fun defExpr -> Assign(name, Expr.Expr(Minus, Var name, defExpr))
            str_ws "/=" >>. pexpr |>> fun defExpr -> Assign(name, Expr.Expr(Divide, Var name, defExpr))
            str_ws "+=" >>. pexpr |>> fun defExpr -> Assign(name, Expr.Expr(Plus, Var name, defExpr))
            str_ws "*=" >>. pexpr |>> fun defExpr -> Assign(name, Expr.Expr(Times, Var name, defExpr))
            str_ws "="  >>. pexpr |>> fun defExpr -> Assign(name, defExpr)
        ]

    pImplicitVarWhenAssign notFollowedByBinOpIdent .>>? ws
    >>=? assdef

let textOutside: _ Parser =
    appendToken Tokens.Text
        (manyStrings
            (choice [
                many1Satisfy (isNoneOf " \n&;/")
                ws1Take .>>? notFollowedBy (satisfy (isAnyOf "\n&;"))
                pstring "/" .>>? notFollowedByString "*"
            ]))
let pvar varHighlightKind (range, (varName:string)) =
    let msg =
        Defines.vars
        |> Map.tryFind (varName.ToLower())
        |> function
            | Some dscr -> dscr
            | None ->
                "Пользовательская глобальная переменная числового типа"
    appendToken2 Tokens.Variable range
    >>. appendHover2 (RawDescription msg) range
    >>. appendVarHighlight range varName varHighlightKind

let psub: _ Parser =
    let psub, psubref = createParserForwardedToRef()
    let pansiCode =
        appendToken Tokens.TokenType.InterpolationBegin (pchar '#')
        >>? pchar '#'
        >>? appendToken Tokens.TokenType.ConstantNumericInteger pint32
        |>> (char >> SubAsciiChar)
        .>> appendToken Tokens.TokenType.InterpolationEnd (pchar '$')
    let pspace =
        appendToken Tokens.TokenType.InterpolationBegin (pchar '#')
        >>? appendToken Tokens.TokenType.InterpolationEnd (pchar '$')
        >>% SubSpace
    let ident =
        many1Satisfy (isNoneOf "#$\n")

    let p2 =
        applyRange ident
        .>>? appendToken Tokens.TokenType.InterpolationEnd (pchar '$')
        >>= fun (r, name) ->
            pvar ReadAccess (r, name)
            >>% SubVar name

    let p =
        let p = psub <|> (ident |>> fun name -> SubVar name)
        appendToken Tokens.TokenType.InterpolationBegin (pchar '#')
        >>. opt (pchar '%')
            >>= fun isStr ->
                p2 |>> fun x -> Subs(Option.isSome isStr, [x])
                <|> (many1 p |>> fun x -> Subs(Option.isSome isStr, x)
                     .>> appendToken Tokens.TokenType.InterpolationEnd (pchar '$'))

    psubref := pansiCode <|> pspace <|> p
    psub

let link: _ Parser =
    appendToken Tokens.TokenType.InterpolationBegin (pstring "[[")
    >>. applyRange
            (many1Strings
                (many1Satisfy (isNoneOf "|\n]")
                 <|> (pstring "]" .>>? notFollowedByString "]")))
    .>>. opt
            (pchar '|'
             >>. applyRange
                     (many1Strings
                        (many1Satisfy (isNoneOf "\n]")
                         <|> (pstring "]" .>>? notFollowedByString "]"))))
    .>> appendToken Tokens.TokenType.InterpolationBegin (pstring "]]")
    >>= fun ((textRange, text), locName) ->
            match locName with
            | Some(locRange, locName) ->
                appendToken2 Tokens.TokenType.Text textRange
                >>. applyLoc(locRange, locName)
                >>% (text, locName)
            | None ->
                applyLoc(textRange, text)
                >>% (text, text)

let ptext =
    let notFollowedByElse =
        skipStringCI "else"
        .>> (skipSatisfy (not << isIdentifierChar)
             <|> eof)
    applyRange
        (many1Strings
            (choice [
                many1Satisfy (isNoneOf " \n&;/#[")
                ws1Take .>>? notFollowedBy (skipSatisfy (isAnyOf "\n&;") <|> notFollowedByElse)
                pstring "/" .>>? notFollowedByString "*"
                pstring "[" .>>? notFollowedByString "["
                // skipNewline >>? pchar '_' >>% ""
            ]))
    // many1 (p <|> (skipNewline >>? pchar '_' >>. p))
let textInside: Text Parser =
    many
        (ptext >>= fun (r, x) -> appendToken2 Tokens.Text r >>% JustText x
         <|> (psub |>> Substitution)
         <|> (link |>> Link))
let pinv pcontent: _ Parser =
    // * `inv expr, itemName`

    // * `inv- item`
    // * `inv+ itemName` or `inv itemName`
    let p1 =
        let p =
            (skipChar '-' >>% 1)
            <|> (skipChar '+' >>% -1)
        tuple2
            ((ws1 >>. opt p
             <|> (p |>> Some))
             |>> (Option.defaultValue 1
                  >> fun x -> Val (Int x) )
            )
            pcontent
    appendToken Tokens.Procedure
        (pstringCI "inv")
    >>? (notFollowedBy
            (skipManySatisfy (isNoneOf "\n,&") >>. skipSatisfy (isAnyOf ",")) >>. p1
         <|> (followedBy (skipSatisfy (isAnyOf "+-")) <|> ws1
              >>? pexpr .>> ws .>> pchar ',' .>> ws .>>. pcontent)
         |>> Inv)
let plnOutside pcontent: _ Parser =
    appendToken Tokens.Procedure
        (pstringCI "pln" <|> pstringCI "println" >>% true
         <|> (pstringCI "print" <|> pstringCI "p" >>% false))
    .>>.? ((skipNewline >>% []) <|> (ws1 >>. pcontent))
    |>> P
let gotoOutside pcontent: _ Parser =
    let p =
        ptext .>>. pcontent
        >>= fun ((locRange, locName), xs) ->
            if List.isEmpty xs then
                applyLoc(locRange, locName)
                >>% [JustText locName]
            else
                appendToken2 Tokens.Text locRange
                >>% (JustText locName)::xs

    appendToken Tokens.Procedure
        (pstringCI "goto" >>% false
         <|> (pstring "proc" >>% true))
    .>>.? (ws1 >>. (p <|> pcontent))
    |>> Goto

let punknownProc =
    applyRange notFollowedByBinOpIdent
    .>>. textInside
    >>= fun ((range, name), text) ->
        let p =
            [
                "Такой процедуры нет, а если есть, то напишите мне, автору расширения, пожалуйста, и я непременно добавлю."
                "Когда-нибудь добавлю: 'Возможно, вы имели ввиду: ...'"
            ]
            |> String.concat "\n"
            |> appendSemanticError range
        appendToken2 Tokens.TokenType.Procedure range
        >>. p
        >>% RawProc(name, text)

let pcallProc : _ Parser =
    let f defines p =
        applyRange p
        >>= fun (range, name) ->
            let p =
                defines
                |> Map.tryFind (String.toLower name)
                |> function
                    | Some (dscr, sign) ->
                        appendHover2 (RawDescription dscr) range
                        >>% Some sign
                    | None ->
                        [
                            "Такой процедуры нет, а если есть, то напишите мне, автору расширения, пожалуйста, и я непременно добавлю."
                            "Когда-нибудь добавлю: 'Возможно, вы имели ввиду: ...'"
                        ]
                        |> String.concat "\n"
                        |> appendSemanticError range
                        >>% None
            appendToken2 Tokens.TokenType.Procedure range
            >>. p
            |>> fun sign -> name, range, sign
    let pProcWithAsterix: _ Parser =
        let p =
            pchar '*' >>. many1Satisfy isIdentifierChar
            |>> sprintf "*%s" // да, так и хочется использоваться `many1Satisfy2`, но она довольствуется лишь первым символом, то есть '*', потому не подходит

        f Defines.proceduresWithAsterix p

    let procHoverAndToken =
        f Defines.procs notFollowedByBinOpIdent

    let pDefProc : _ Parser =
        Defines.procs
        |> Seq.sortByDescending (fun (KeyValue(name, _)) -> name) // для жадности
        |> Seq.map (fun (KeyValue(name, (dscr, sign))) ->
            applyRange (pstringCI name .>>? notFollowedVarCont)
            >>= fun (range, name) ->
                appendToken2 Tokens.TokenType.Procedure range
                >>. appendHover2 (RawDescription dscr) range
                >>% (name, range, sign)
        )
        |> List.ofSeq
        |> choice
    /// Особый случай, который ломает к чертям весь заявленный синтаксис
    let adhoc =
        let createIdent name =
            pstringCI name .>>? notFollowedVarCont
        let p name name2 =
            createIdent name .>>? ws1 .>>.? createIdent name2
        applyRange
            ((p "add" "obj"
              <|> (createIdent "del" .>>? ws1 .>>.? (createIdent "obj" <|> createIdent "act"))
              |>> fun (name1, name2) -> name1 + name2)
             <|> (p "close" "all" |>> fun (name1, name2) -> sprintf "%s %s" name1 name2))
        >>= fun (range, name) ->
            match Map.tryFind (String.toLower name) Defines.procs with
            | Some (dscr, sign) ->
                appendToken2 Tokens.TokenType.Procedure range
                >>. appendHover2 (RawDescription dscr) range
                >>% (name, range, sign)
            | None -> failwithf "'%s' not found in predef procs" name
    // pProcWithAsterix
    // .>> ws .>>. sepBy (applyRange pexpr) (char_ws ',') // Кстати, `,` — "punctuation.separator.parameter.js"
    // <|> (adhoc <|> pDefProc .>> ws
    //      .>>. (followedBy (skipNewline <|> skipChar '&' <|> eof) >>% []
    //            <|> bet_ws '(' ')' (sepBy (applyRange pexpr) (pchar ',' >>. ws))
    //            <|> sepBy1 (applyRange pexpr) (char_ws ','))
    //      |>> fun ((name, range, sign), args) -> ((name, range, Some sign), args))
    // <|> (procHoverAndToken
    //      .>>? (ws1 <|> followedBy (satisfy (isAnyOf "'\"")))
    //      .>>.? sepBy1 (applyRange pexpr) (char_ws ','))
    // >>= fun ((name, range, sign), args) ->
    //     match sign with
    //     | None ->
    //         preturn (Proc(name, List.map snd args))
    //     | Some x ->
    //         let procNameLower = String.toLower name
    //         let pLoc =
    //             if Set.contains procNameLower Defines.transferOperatorsSet then
    //                 match args with
    //                 | (r, Val (String [[StringKind locName]]))::_ ->
    //                     getUserState
    //                     >>= fun (x:State) ->
    //                     let nested =
    //                         if x.SingleQuotNestedCount > x.DoubleQuotNestedCount then // TODO: ничего хорошего из этого не получится
    //                             x.SingleQuotNestedCount
    //                         else
    //                             x.DoubleQuotNestedCount
    //                         |> (+) 1
    //                     let r =
    //                         { r with
    //                             Column1 = r.Column1 + int64 nested // чтобы `'` или `"` пропустить
    //                             Column2 = r.Column2 - int64 nested
    //                         }
    //                     let locNameLower = String.toLower locName
    //                     appendLocHighlight r locNameLower VarHighlightKind.ReadAccess
    //                     >>. pGetDefLocPos locNameLower
    //                         >>= function
    //                             | None ->
    //                                 updateUserState (fun st ->
    //                                     { st with
    //                                         NotDefinedLocs =
    //                                             st.NotDefinedLocs
    //                                             |> Map.addOrMod locNameLower [r] (fun xs -> r::xs)
    //                                     }
    //                                 )
    //                             | Some _ -> preturn ()
    //                 | _ -> preturn ()
    //             else
    //                 preturn ()
    //         args
    //         |> Array.ofList
    //         |> Defines.getFuncByOverloadType x
    //         |> function
    //             | None ->
    //                 let msg =
    //                     Defines.Show.printSignature name x
    //                     |> sprintf "Ожидается одна из перегрузок:\n%s"
    //                 appendSemanticError range msg
    //             | Some () ->
    //                 preturn ()
    //         >>. pLoc
    //         >>% Proc(name, List.map snd args)

    choice [
        plnOutside textInside
        gotoOutside textInside
        pinv textInside
    ]
let blockComment : _ Parser =
    appendToken Tokens.PunctuationDefinitionComment (pstring "/*")
    >>. manyStrings
            (appendToken Tokens.Comment
                (many1Strings
                    (many1Satisfy (isNoneOf "*\n")
                     <|> (pstring "*" .>>? notFollowedByString "/")))
            <|> newlineReturn "\n")
    .>> appendToken Tokens.PunctuationDefinitionComment (pstring "*/")
    |>> BlockComment
let inlineComment : _ Parser =
    appendToken Tokens.PunctuationDefinitionComment (pchar ';')
    >>. appendToken Tokens.Comment
            (manySatisfy ((<>) '\n'))
    |>> Comment

let genKeywordParser tokenType keyword =
    let dscr =
        Defines.keywords
        |> List.tryPick (fun (name, dscr) ->
            if name = keyword then Some dscr
            else None)
        |> Option.defaultWith (fun () -> failwithf "not found %s" keyword)
    appendTokenHover tokenType (RawDescription dscr)
        (pstringCI keyword .>>? notFollowedVarCont)

let pendKeyword : _ Parser =
    genKeywordParser Tokens.TokenType.End "end"

let pstmts' pstmt =
    many
        (pstmt .>> spaces
         .>> (skipMany (ppunctuationTerminator .>> spaces)))
let pstmts1' pstmt =
    many1
        (pstmt .>> spaces
         .>> (skipMany (ppunctuationTerminator .>> spaces)))
let pstmt =
    let underscore = newline >>? skipChar '_' >>. ws
    let pstmt, pstmtRef = createParserForwardedToRef<PosStatement, _>()
    let pInlineStmts =
        many (pstmt .>> ws .>> skipMany (ppunctuationTerminator >>. ws <|> underscore))
    let pInlineStmts1 =
        many1 (pstmt .>> ws .>> skipMany (ppunctuationTerminator >>. ws <|> underscore))
    let pstmts = pstmts' pstmt

    let pIf =
        let pthenKeyword : _ Parser =
            genKeywordParser Tokens.TokenType.Then "then"
        let pifKeyword : _ Parser =
            genKeywordParser Tokens.TokenType.If "if"
        let pelseKeyword : _ Parser =
            genKeywordParser Tokens.TokenType.Else "else"
        let pifHeader = pifKeyword .>> ws >>. pexpr .>> pthenKeyword

        let pElse1 =
            pelseKeyword .>> (ws >>. optional underscore)
            >>. (pInlineStmts1 .>> opt pthenKeyword
                 <|> (spaces >>. pstmts .>> pthenKeyword))
        pipe3
            (pifHeader .>> (ws >>. optional underscore))
            (pInlineStmts1 .>> ws)
            (opt pElse1)
            (fun expr thenBody elseBody ->
                If(expr, thenBody, Option.defaultValue [] elseBody))

    let p =
        choice [
            blockComment
            inlineComment
            pendKeyword >>% End
            pIf
            psub |>> SubStmt
            pcallProc |>> Proc
            pAssign pstmts

            punknownProc |>> Proc
        ]
    pstmtRef := (getPosition |>> (fparsecPosToPos >> NoEqualityPosition)) .>>.? p
    pstmt

let pstmts = pstmts' pstmt
let pstmts1 = pstmts1' pstmt

let psharpKeyword : _ Parser =
    appendToken Tokens.TokenType.SharpBeginLoc (pchar ':')

let plocHeader =
    psharpKeyword .>> ws
    >>. (applyRange
            (many1Strings
                (many1Satisfy (isNoneOf " \t\n")
                 <|> (many1Satisfy (isAnyOf " \t") .>>? notFollowedByNewline))
             <?> "location name")
          >>= fun (r, name) ->
            let pCheckLocExists r2 locName =
                pGetDefLocPos locName
                >>= function
                    | Some r ->
                        sprintf "Локация уже определена в\n%A" r
                        |> appendSemanticError r2
                    | None -> preturn ()

            let locNameLower = String.toLower name
            pCheckLocExists r locNameLower
            >>. updateUserState (fun st ->
                    { st with
                        NotDefinedLocs =
                            Map.remove locNameLower st.NotDefinedLocs
                    }
                )
            >>. appendLocHighlight r locNameLower VarHighlightKind.WriteAccess
            >>. appendToken2 Tokens.TokenType.NameLabel r
            >>. preturn name
         )
let ploc =
    tuple2 (plocHeader .>> spaces) pstmts

let emptyState =
    { emptyState with PStmts = pstmts }
let pstart =
    spaces
    >>. tuple2 (opt (plocHeader .>> spaces)) pstmts
    .>>. many (ploc .>> spaces)
    .>> (getPosition >>= fun p ->
            updateUserState (fun st ->
                { st with LastSymbolPos = p}))
    |>> fun (firstLoc, restLocs) ->
        {| FirstLoc = firstLoc; Locations = restLocs |} : Locations
let start str =
    runParserOnString (pstart .>> eof)
        emptyState
        ""
        str
let startOnFile enc path =
    runParserOnFile (pstart .>> eof)
        emptyState
        path
        enc
