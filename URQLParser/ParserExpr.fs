module Qsp.Parser.Expr
open FParsec
open FsharpMyExtension
open FsharpMyExtension.Either
open Qsp
open Qsp.Ast
open Qsp.Parser.Generic
open Qsp.Tokens

let pbinaryOperator : _ Parser =
    [
        Defines.exprNamedOperators |> List.map (fun (x, _, _) -> x)
        Defines.keywords |> List.map fst
    ]
    |> List.concat
    |> List.sortDescending
    |> List.map pstringCI
    |> choice

/// берёт только то, что начинается с `#` или `$`
let pexplicitVar varHighlightKind : _ Parser =
    let isIdentifierFirstChar c = isLetter c || c = '_'
    let p = many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier"
    // TODO: или просто `many1Satisfy isIdentifierChar` ?
    let varType =
        choice [
            pchar '#' >>% ExplicitNumericType
            pchar '$' >>% StringType
        ]

    (getPosition .>>.? varType) .>>. (p .>>. getPosition)
    >>= fun ((p1, typ), (varName, p2)) ->
        let range = toRange p1 p2
        let msg =
            match typ with
            | StringType ->
                Defines.vars
                |> Map.tryFind (sprintf "$%s" (varName.ToLower()))
                |> function
                    | Some dscr -> dscr
                    | None -> "Пользовательская глобальная переменная строчного типа"
            | ExplicitNumericType ->
                Defines.vars
                |> Map.tryFind (sprintf "#%s" (varName.ToLower()))
                |> function
                    | Some dscr -> dscr
                    | None -> "Пользовательская глобальная переменная числового типа"
            | ImplicitNumericType -> failwith "Not Implemented"
        appendToken2 Tokens.Variable range
        >>. appendHover2 (RawDescription msg) range
        >>. appendVarHighlight range (typ, varName) varHighlightKind
        >>. preturn (typ, varName)
type ProcOrFunc =
    | Procedure of string
    | Function of string

let notFollowedByBinOpIdent =
    let p =
        pbinaryOperator
        .>> (skipSatisfy (not << isIdentifierChar)
             <|> eof)
    let p2 =
        notFollowedByL p "keyword"
        >>. ident
    p2
let ws =
    ws
    >>. skipMany
            (appendToken TokenType.Underscore (pchar '_')
             >>? ((ws1 >>? skipNewline) <|> skipNewline) >>. spaces)

let identWithSpaces =
    // https://github.com/fireton/fireurq/blob/406e835f3dc07aecd65d0726d1546c356f3b1f0a/furqTypes.pas#L55
    let ident =
        many1Satisfy2L
            (fun c -> isLetter c || c = '_')
            (fun c -> isLetter c || c = '_' || isDigit c )
            "identifier"
    // https://github.com/fireton/fireurq/blob/2a4f9d8fe29b174bfa21112336550a59f50ecbee/furqExprEval.pas#L346
    let notFollowedByBinOpIdent =
        let p =
            pbinaryOperator
            .>> (skipSatisfy (not << isIdentifierChar)
                 <|> eof)
        notFollowedByL p "keyword"
        >>. ident
    pipe2
        notFollowedByBinOpIdent
        (many (ws1Take .>>.? notFollowedByBinOpIdent |>> fun (ws, xs) -> [ws; xs]))
        (fun x y -> x :: List.concat y |> System.String.Concat)

let invHas : _ Parser =
    appendToken TokenType.Procedure (pstringCI "inv_")
    >>. ws
    >>. appendToken TokenType.Variable identWithSpaces
    |>> InvHas
let term expr =
    let getDesc (varType, (name:string)) =
        match varType with
        | StringType ->
            Defines.vars
            |> Map.tryFind (sprintf "$%s" (name.ToLower()))
            |> function
                | Some dscr -> dscr
                | None -> "Пользовательская глобальная переменная строчного типа"
        | ExplicitNumericType ->
            Defines.vars
            |> Map.tryFind (sprintf "#%s" (name.ToLower()))
            |> function
                | Some dscr -> dscr
                | None -> "Пользовательская глобальная переменная числового типа"
        | ImplicitNumericType ->
            Defines.vars
            |> Map.tryFind (name.ToLower())
            |> function
                | Some dscr -> dscr
                | None ->
                    "Пользовательская глобальная переменная числового типа"
    let pterm, ptermRef = createParserForwardedToRef()
    let pcallFuncOrArrOrVar =
        let pBracesArgs =
            bet_ws '(' ')' (sepBy expr (pchar ',' >>. ws))
        let pcallFunctionOrArrOrVar =
            let pimplicitVar =
                notFollowedByBinOpIdent |>> fun x -> ImplicitNumericType, x
            let pexplicitVar =
                let isIdentifierFirstChar c = isLetter c || c = '_'
                let p = many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier"
                // TODO: или просто `many1Satisfy isIdentifierChar` ?
                let varType =
                    choice [
                        pchar '#' >>% ExplicitNumericType
                        pchar '$' >>% StringType
                    ]
                varType .>>. p

            tuple2
                (applyRange (pexplicitVar <|> pimplicitVar) .>> ws)
                ((pBracesArgs
                  |>> fun args ->
                    let tokenType = TokenType.Function
                    fun (funType, name) range ->
                        let p =
                            [
                                "Такой функции нет, а если есть, то напишите мне, автору расширения, пожалуйста, и я непременно добавлю."
                                "Когда-нибудь добавлю: 'Возможно, вы имели ввиду: ...'"
                            ]
                            |> String.concat "\n"
                            |> appendSemanticError range
                        p
                        >>. appendToken2 tokenType range
                        >>% Func(Undef name, args)
                    )
                //   Невозможно, поскольку неоднозначно трактуется `f+1` => `f(+1)` или `f + 1`
                //   <|> (pterm |>> fun arg -> TokenType.Function, fun (typ', name) -> Func(name, [arg]))
                  <|>% fun (varType, nameVar) range ->
                        let desc = getDesc(varType, nameVar)
                        appendHover2 (RawDescription desc) range
                        >>. appendToken2 TokenType.Variable range
                        >>. appendVarHighlight range (varType, nameVar) VarHighlightKind.ReadAccess
                        >>% Var(varType, nameVar))
            >>= fun ((range, (varType, name)), f) ->
                    f (varType, name) range
        // #load @"Defines.fs"
        // open Qsp
        let nullary, multiary =
            Defines.functionsByName
            |> Map.partition (fun _ x ->
                let x, _ = x.Signature
                match x with
                | Defines.JustOverloads []
                | Defines.JustOverloads [([||], ())] -> true
                | _ -> false
            )
        let nullaryFunc =
            nullary
            |> Seq.sortByDescending (fun (KeyValue(name, _)) -> name) // для жадности
            |> Seq.map (fun (KeyValue(name, x)) ->
                applyRange (opt (pchar '$') >>? pstringCI name .>>? notFollowedVarCont)
                >>= fun (range, name) ->
                    appendToken2 TokenType.Function range
                    >>. appendHover2 (FuncDescription x.SymbolicName) range
                    >>% (name, range, x)
            )
            |> List.ofSeq
            |> choice

        let pPreDefFunc =
            multiary
            |> Seq.sortByDescending (fun (KeyValue(name, _)) -> name) // для жадности
            |> Seq.map (fun (KeyValue(name, x)) ->
                applyRange (opt (pchar '$') >>? pstringCI name .>>? notFollowedVarCont)
                >>= fun (range, name) ->
                    appendToken2 TokenType.Function range
                    >>. appendHover2 (FuncDescription x.SymbolicName) range
                    >>% (name, range, x)
            )
            |> List.ofSeq
            |> choice
        nullaryFunc .>>. (ws >>. (pBracesArgs <|>% []))
        <|> (pPreDefFunc .>> ws .>>. (pBracesArgs <|> (pterm |>> List.singleton) <|>% []))
        >>= fun ((stringName, range, x), args) ->
                let sign, returnType = x.Signature
                let p =
                    args
                    |> Array.ofList
                    |> Defines.getFuncByOverloadType sign
                    |> function
                        | None ->
                            let msg =
                                Defines.Show.printFuncSignature stringName returnType sign
                                |> sprintf "Ожидается одна из перегрузок:\n%s"
                            appendSemanticError range msg
                        | Some () ->
                            preturn ()
                p
                >>% Func(Predef x.SymbolicName, args)
        <|> pcallFunctionOrArrOrVar
    let customFuncs =
        invHas
    let pval =
        choice [
            // TODO: `pbraces` — он точно нужен?
            stringLiteralWithToken expr |>> String
            appendToken TokenType.ConstantNumericInteger
                (pint32 |>> Int)
        ]
        |>> Val
    ptermRef := pval <|> pcallFuncOrArrOrVar
    pval <|> customFuncs <|> pcallFuncOrArrOrVar <|> bet_ws '(' ')' expr

let pExprNew : _ Parser =
    let pExpr, pExprRef = createParserForwardedToRef()
    let term = term pExpr
    let pchar c typ =
        appendToken typ (pchar c)
    let pstringCI c typ =
        appendToken typ (pstringCI c)
    let pstring c typ =
        appendToken typ (pstring c)

    let pNeg =
        pchar '-' (TokenType.UnaryOperator Neg) >>. ws >>. term
        |>> fun e1 -> UnarExpr(Neg, e1)
        <|> (pchar '+' (TokenType.UnaryOperator Positive) >>. ws >>. term)
    let pProd =
        chainl1 (pNeg <|> term .>> ws)
            ((pchar '*' (TokenType.BinaryOperator Times) >>% Times
              <|> (pchar '/' (TokenType.BinaryOperator Divide) >>% Divide))
             .>> ws |>> fun op e1 e2 -> Expr(op, e1, e2))
    let pSum =
        chainl1 (pProd .>> ws)
            ((pchar '+' (TokenType.BinaryOperator Plus) >>% Plus
              <|> (pchar '-' (TokenType.BinaryOperator Minus) >>% Minus))
             .>> ws |>> fun op e1 e2 -> Expr(op, e1, e2))
    let pCompare pNo =
        chainl1 (pNo <|> pSum .>> ws)
            (choice [
                pstring "==" (TokenType.BinaryOperator Similar) >>% Similar
                pchar '=' (TokenType.BinaryOperator Eq) >>% Eq

                pstring "<>" (TokenType.BinaryOperator Ne) >>% Ne
                pstring "<=" (TokenType.BinaryOperator Le) >>% Le
                pchar '<' (TokenType.BinaryOperator Lt) >>% Lt

                pstring ">=" (TokenType.BinaryOperator Ge) >>% Ge
                pchar '>' (TokenType.BinaryOperator Gt) .>>? notFollowedBy (FParsec.CharParsers.pchar '>') >>% Gt // чтобы исключить `>>`
             ]
             .>> ws |>> fun op e1 e2 -> Expr(op, e1, e2))

    let pNo =
        // TODO: `no` — ассоциативный оператор, потому допустимо такое: `no (no -1)`
        let pNo, pNoRef = createParserForwardedToRef()
        pNoRef :=
            pstringCI "not" TokenType.Procedure >>? notFollowedVarCont >>. ws >>. pCompare pNo
            |>> fun e1 -> UnarExpr(Not, e1)
        pCompare pNo .>> ws
    let pAnd =
        chainl1 (pNo .>> ws)
            ((pstringCI "and" TokenType.Procedure >>? notFollowedVarCont >>. ws >>% And)
             .>> ws |>> fun op e1 e2 -> Expr(op, e1, e2))
    let pOr =
        chainl1 (pAnd .>> ws)
            ((pstringCI "or" TokenType.Procedure >>? notFollowedVarCont >>. ws >>% Or)
             .>> ws |>> fun op e1 e2 -> Expr(op, e1, e2))

    pExprRef := pOr
    pExpr
let pexpr = pExprNew
