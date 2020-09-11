open Fuchu
open FsharpMyExtension
open FsharpMyExtension.Either
open FParsec
open Qsp
open Qsp.Ast
open Qsp.Parser
open Qsp.Parser.Generic
open Qsp.Parser.Main


[<Tests>]
let simpleTest =
    testCase "simpleTest" (fun _ ->
        let exp = "a"
        let act = "a"
        Assert.Equal("msg", exp, act)
    )
// run simpleTest // <- если нужно запустить тест вручную

[<Tests>]
let plnOutsideTest =
    testList "plnOutside" [
        testCase "pln text & after" (fun _ ->
            let exp = Pln [JustText "text"]
            let st, act = runStateEither (plnOutside textInside) Generic.emptyState "pln text & after"
            Assert.Equal("", Right exp, act)
        )
        testCase "testCase2" (fun _ ->
            let exp = Pln [JustText "text"]
            let st, act = runStateEither (plnOutside textInside) Generic.emptyState "pln text\n"
            Assert.Equal("", Right exp, act)
        )
        testCase "testCase3" (fun _ ->
            let exp = ()
            let act = ()
            Assert.Equal("msg3", exp, act)
        )
    ]
// run simpleTestList

[<EntryPoint;System.STAThread>]
let main arg =
    defaultMainThisAssembly arg
