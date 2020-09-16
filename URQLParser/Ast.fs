module Qsp.Ast
open FsharpMyExtension
open Qsp

[<Struct>]
type Position = { StreamName:string; Index:int64; Line:int64; Column:int64 }
let positionCreate streamName index line column =
    { StreamName = streamName; Index = index; Line = line; Column = column }
let positionEmpty =
    positionCreate "" 0L 0L 0L

type NoEqualityPosition(pos:Position) =
    member __.Pos = pos
    override __.ToString() = pos.ToString()
    override __.Equals _ = true
    override __.GetHashCode() = 0

let test () =
    let x = NoEqualityPosition(positionCreate "" 0L 0L 0L)
    let y = NoEqualityPosition(positionCreate "" 0L 0L 1L)
    x = y

type LocationName = string

[<Struct>]
type Op =
    /// `+`
    | Plus
    /// `-`
    | Minus
    /// `*`
    | Times
    /// `/`
    | Divide

    /// `==`
    | Similar
    /// `=`
    | Eq
    /// `>`
    | Gt
    /// `>=`
    | Ge
    /// `&lt;`
    | Lt
    /// `&lt;=`
    | Le
    /// `&lt;>`
    | Ne

    /// `and`
    | And
    /// `or`
    | Or
type IsBinOpSymbolic = bool
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
[<RequireQualifiedAccess>]
module Op =
    [<ReflectedDefinition>]
    let toString = function
        | Times -> "*"
        | Divide -> "/"
        | Plus -> "+"
        | Minus -> "-"
        | Lt -> "<"
        | Gt -> ">"
        | Le -> "<="
        | Ge -> ">="
        | Ne -> "<>"
        | And -> "and"
        | Or -> "or"
        | Eq -> "="
        | Similar -> "=="

    let ops =
        Reflection.Reflection.unionEnum<Op>
        |> Array.map (fun x ->
            let IsBinOpSymbolic opName =
                not <| String.exists System.Char.IsLetter opName
                : IsBinOpSymbolic
            let y = toString x
            x, (y, IsBinOpSymbolic y) )

    let fromString =
        let m = Array.map (fun (a, b) -> b, a) ops |> Map.ofArray
        fun x -> match Map.tryFind x m with Some x -> x | None -> failwithf "not found %A" x
[<Struct>]
type UnarOp =
    /// `-`
    | Neg
    | Not

[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
[<RequireQualifiedAccess>]
module UnarOp =
    [<ReflectedDefinition>]
    let toString = function Neg -> "-" | Not -> "not"
    let ops =
        Reflection.Reflection.unionEnum<UnarOp>
        |> Array.map (fun x -> x, toString x)
    let fromString =
        let m = Array.map (fun (a, b) -> b, a) ops |> Map.ofArray
        fun x -> match Map.tryFind x m with Some x -> x | None -> failwithf "not found %A" x
module Precedences =
    type T = OpB of Op | PrefB of UnarOp

    let prec = function
        | OpB Or -> 1
        | OpB And -> 2
        | PrefB Not -> 3
        // =     | <      | >      | <>     | <=     | >=     | ==
        | OpB Eq | OpB Lt | OpB Gt | OpB Ne | OpB Le | OpB Ge | OpB Similar -> 5
        | OpB Plus | OpB Minus -> 6
        | OpB Times | OpB Divide -> 8
        | PrefB Neg -> 9
[<Struct>]
type VarType =
    /// `varName`, если к такой присвоить строковое значение, то интерпретатор попытается преобразовать ее в число. Если не получится, выбьет ошибку.
    | ImplicitNumericType
    /// `#varName`, если к такой присвоить строковое значение, то интерпретатор попытается преобразовать ее в число. Если не получится, выбьет ошибку.
    | ExplicitNumericType
    /// `$varName`, к такой переменной можно смело присваивать и число, и строку
    | StringType
type 'Predef PredefUndef =
    | Predef of 'Predef
    | Undef of string
type Var = VarType * string
/// `#sub#insub#iside$$fo#bar$o$` -> `(sub(insub(iside))fo(bar)o)`
type Substitution =
    | Subs of isString:bool * Substitution list
    | SubVar of string
    | SubAsciiChar of char
type TextElement =
    | Substitution of Substitution
    | JustText of string
    /// * compact version: `[[текст ссылки]]`
    /// * full version: `[[текст ссылки|название локации]]`
    | Link of text:string * locName:LocationName
type Text = TextElement list
type StmtsOrRaw =
    | Raw of string
    | StaticStmts of PosStatement list
and LineKind =
    | StringKind of string
    /// Это то, что заключено между `&lt;&lt; >>`
    | ExprKind of Expr
    /// `&lt;a href="exec: ...">some text&lt;/a>`
    | HyperLinkKind of StmtsOrRaw * Line list
/// Без переносов
and Line = LineKind list

and Value =
    | Int of int
    | String of Line list

and Expr =
    | Val of Value
    | Var of var:Var
    | InvHas of itemName:string
    | Func of Defines.PredefFunc PredefUndef * Expr list
    | Arr of var:Var * Expr list
    | UnarExpr of UnarOp * Expr
    | Expr of Op * Expr * Expr
and PosStatement = NoEqualityPosition * Statement
and Proc =
    | P of newline:bool * Text
    /// if `returned` is true then `proc` else `goto`
    | Goto of returned:bool * Text
    /// * `inv+ item` or `inv item`
    /// * `inv- item`
    /// * `inv expr, item`
    | Inv of Expr * Text
    | RawProc of string * Text
and Statement =
    | Proc of Proc
    | SubStmt of Substitution
    | Assign of var:Var * Expr
    | If of Expr * PosStatement list * PosStatement list
    | Label of string
    | BlockComment of string
    | Comment of string
    | Exit
    | End

type Locations =
    {|
        FirstLoc: LocationName option * PosStatement list
        Locations: (LocationName * PosStatement list) list
    |}