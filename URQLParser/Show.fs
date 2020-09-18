module Qsp.Show
open FsharpMyExtension
open FsharpMyExtension.ShowList
open Qsp.Ast

type FormatConfig =
    {
        IsSplitStringPl: bool
        TrimWhitespaceWhenSplit: bool
    }
    static member Default =
        {
            IsSplitStringPl = false
            TrimWhitespaceWhenSplit = false
        }

let showVar varName =
    showString varName

let rec showStringLines showExpr showStmtsInline (lines:list<Line>) =
    lines
    |> List.map (
        List.collect (
            function
            | StringKind x ->
                showString (x.Replace("'", "''"))
                |> List.singleton
            | ExprKind x ->
                showExpr x
                |> show
                |> fun x -> x.Replace("'", "''") // TODO: стоит ли говорить, что все эти былины с `.Replace("'", "''")` нужно превратить в нормальный код?
                |> showString
                |> bet "<<" ">>"
                |> List.singleton
            | HyperLinkKind(x, body) ->
                let attValue =
                    match x with
                    | Raw x ->
                        x.Replace("'", "''")
                        |> showString
                    | StaticStmts(x) ->
                        showStmtsInline x
                        |> show
                        |> fun x -> x.Replace("'", "''")
                        |> showString
                let header =
                    showString "<a href=\"exec: "
                    << attValue
                    << showString "\">"
                match showStringLines showExpr showStmtsInline body with
                | [] ->
                    header
                    << showString "</a>"
                    |> List.singleton
                | [x] ->
                    header
                    << x
                    << showString "</a>"
                    |> List.singleton
                | xs ->
                    xs
                    |> List.mapStartMidEnd
                        (fun x -> header << x)
                        id
                        (fun x -> x << showString "</a>")
                    |> fun x -> x // TODO: и все строки позже соединятся воедино, даже пробелов не удостоятся, ага.
        ) >> joinsEmpty empty
    )
let showValue showExpr showStmtsInline = function
    | Int x -> shows x
    | String lines ->
        showStringLines showExpr showStmtsInline lines
        |> joinsEmpty (showString "\n")
        |> bet "'" "'"
let ops = Op.toString >> showString

let unar = function Not -> "not" | Neg -> "-" | Positive -> "+"
let showFuncName = function
    | PredefUndef.Predef name ->
        match Map.tryFind name Qsp.Defines.functionBySymbolic with
        | Some x ->
            let _, returnedType = x.Signature
            let returnedType =
                match returnedType with
                | Defines.Numeric -> id
                | Defines.String -> showChar '$'
                | Defines.Any -> id // TODO: defines by argument type
            let nameStr = (string name).ToLower()
            returnedType << showString nameStr
        | None -> failwithf "%A not found in `functionBySymbolic`" name
    | PredefUndef.Undef name ->
        showString name
let rec simpleShowExpr showStmtsInline expr : ShowS =
    let rec f = function
        | Val v -> showValue (simpleShowExpr showStmtsInline) showStmtsInline v
        | Var v -> showVar v
        | Func(name, args) ->
            let args =
                if List.isEmpty args then
                    empty
                else
                    showParen true (List.map f args |> join ", ")
            showFuncName name << args
        | UnarExpr(op, e) ->
            let space = function Not -> showSpace | Neg | Positive -> id
            let x =
                match e with
                | Expr(_, _, _) ->
                    showParen true (f e)
                | Arr(_, _) // `-(arr[idx])` лучше выглядит, чем `-arr[idx]`?
                | Func(_, _) // `-(func(idx))` лучше выглядит, чем `-(arr(idx))`?
                | InvHas _
                | UnarExpr _
                | Val _
                | Var _ ->
                    space op << f e
            showString (unar op) << x
        | Expr(op, e1, e2) ->
            let f body =
                match body with
                | Val(_)
                | Var _ ->  f body
                | UnarExpr(_, _)
                | Expr(_, _, _) ->
                    showParen true (f body)
                | Func(_, _)
                | InvHas _
                | Arr(_, _) ->
                    f body
            f e1 << showSpace
            << ops op << showSpace
            << f e2
        | Arr(var, es) ->
            showVar var << bet "[" "]" (List.map f es |> join ", ")
        | InvHas(itemName) -> showString "inv_" << showString itemName
    f expr
let rec showExpr showStmtsInline = function
    | Val v -> showValue (showExpr showStmtsInline) showStmtsInline v
    | Var v -> showVar v
    | Func(name, args) ->
        let args =
            if List.isEmpty args then
                empty
            else
                showParen true
                    (List.map (showExpr showStmtsInline) args |> join ", ")
        showFuncName name << args
    | InvHas(itemName) -> showString "inv_" << showString itemName
    | UnarExpr(op, e) ->
        let space = function Not -> showSpace | Neg | Positive -> id
        showString (unar op) << space op << showExpr showStmtsInline e
    | Expr(op, e1, e2) ->
        let prec = Precedences.OpB >> Precedences.prec
        let f = function
            | Expr(op', _, _) -> showParen (prec op > prec op')
            | UnarExpr _ -> showParen true | _ -> id
        let f x = f x (showExpr showStmtsInline x)
        f e1 << showSpace << ops op << showSpace << f e2
    | Arr(var, es) -> showVar var << bet "[" "]" (List.map (showExpr showStmtsInline) es |> join ", ")


type IndentsOption =
    | UsingSpaces of int
    | UsingTabs

let spaceBetween (s:ShowS) : ShowS =
    showSpace << s << showSpace

let rec showSub sub =
    let brace p = showChar '#' << p << showChar '$'
    match sub with
    | SubVar x -> showString x
    | Subs(isStr, x) ->
        brace
            (if isStr then showChar '%' else id
             << join "" (List.map showSub x))
    | SubAsciiChar c -> brace (showChar '#' << shows (int c))
    | SubSpace -> brace id
let showText (xs:Text) : ShowS =
    xs
    |> List.map (
        function
        | JustText str ->
            showString str
        | Substitution sub ->
            showSub sub
        | Link(text, locName) ->
            let body =
                if text = locName then
                    showString text
                else
                    showString text << showChar '|' << showString locName
            showString "[["
            << body
            << showString "]]"
    )
    |> join ""
let showLabelCall showStmtsInline ((locName, args):LabelCall) =
    let args =
        if List.isEmpty args then
            id
        else
            showParen true (List.map (showExpr showStmtsInline) args |> join ", ")
    showString locName << args

let showProc showStmtsInline = function
    | RawProc(name, e) ->
        let args =
            if List.isEmpty e then
                empty
            else
                showSpace << showText e
        showString name << args
    | P(nl, str) ->
        if nl then showString "pln"
        else showString "p"
        << showSpace << showText str
    | Goto(returned, lab) ->
        if returned then showString "proc" else showString "goto"
        << showSpace << showText lab
    | Inv(e, str) ->
        match e with
        | Val (Int x) when x = 1 || x = -1 ->
            showString "inv"
            << if x > 0 then id else showChar '-'
            << showSpace << showText str
        | e ->
            showString "inv"
            << showSpace << showExpr showStmtsInline e
            << showChar ',' << showSpace << showText str
    | Btn(labelCall, text) ->
        showLabelCall showStmtsInline labelCall
        << showChar ','
        << showSpace << showText text
let showStmt indentsOption (formatConfig:FormatConfig) =
    let tabs =
        match indentsOption with
        | UsingTabs ->
            showChar '\t'
        | UsingSpaces spacesCount ->
            replicate spacesCount ' '
    let rec f' (pos, stmt) =
        let showStmtsInline xs : ShowS =
            List.collect f' xs
            |> joins (showSpace << showChar '&' << showSpace)
        let showAssign = showVar
        let showExpr = showExpr showStmtsInline
        let showStringLines = showStringLines showExpr showStmtsInline
        match stmt with
        | Assign(name', Expr((Plus|Minus) as op, Var name, e)) when name' = name ->
            [showAssign name' << spaceBetween (ops op << showChar '=') << showExpr e]
        | Assign(name', Expr((Plus|Minus) as op, e, Var name)) when name' = name ->
            [showAssign name' << spaceBetween (showChar '=' << ops op) << showExpr e]
        | Assign(ass, e) ->
            [showAssign ass << spaceBetween (showChar '=') << showExpr e]
        | Label s -> [showChar ':' << showString s]
        | If(e, thenBody, elseBody) ->
            let ifHeader e = showString "if" << showSpace << showExpr e << showSpace << showString "then"
            [
                ifHeader e
                << showSpace << showStmtsInline thenBody
                << if List.isEmpty elseBody then id
                   else
                    showSpace << showString "else"
                    << showSpace << showStmtsInline elseBody
            ]
        | Comment s -> [showChar ';' << showString s]
        | Exit -> [showString "exit"]
        | BlockComment str -> [showString "/*" << showString str << showString "*/"]
        | End -> [showString "end"]
        | SubStmt x -> [showSub x]
        | Proc x -> [showProc showStmtsInline x]
    f'

let showLoc indentsOption isSplitStringPl (name, statements) : ShowS list =
    [
        yield showString ": " << showString name
        yield! List.collect (showStmt indentsOption isSplitStringPl) statements
    ]

let printLocs indentsOption isSplitStringPl (xs:Locations) =
    let firstLoc =
        let name, body = xs.FirstLoc
        [
            match name with
            | Some name ->
                yield showString ": " << showString name
            | None -> ()
            yield! List.collect (showStmt indentsOption isSplitStringPl) body
        ]
    let xs =
        List.map (lines << showLoc indentsOption isSplitStringPl) xs.Locations
    lines firstLoc :: xs
    |> joinEmpty "\n\n"
    |> show
