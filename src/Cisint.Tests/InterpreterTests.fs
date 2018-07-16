module InterpreterTests

open Cisint.Core
open Expression
open System
open Xunit
open System.Collections.Generic
open InterpreterState
open Cisint.Tests.TestInputs
open FSharp.Control.Tasks.V2
open TypesystemDefinitions
open StateProcessing
let testMethod =
    let t = (CecilTools.convertType typeof<Something>)
    fun name -> t.Definition.Methods |> Seq.find (fun m -> m.Name = name) |> MethodRef

let state = ExecutionState.Empty
let dispatcher = Interpreter.createSynchronousDispatcher (fun x -> ())

printfn "Current directory is %s" (IO.Directory.GetCurrentDirectory())

let interpretMethod method name state args =
    task {
        let methodRef = (testMethod method)
        let! result = Interpreter.interpretMethod methodRef state args dispatcher
        // waitForDebug()
        let result = { result with Stack = List.map (fun a -> stackConvert a methodRef.ReturnType |> ExprSimplifier.simplify (AssumptionSet.add [SExpr.ImmConstant true] state.Assumptions)) result.Stack }
        let stateDump = ExprFormat.dumpState result
        IO.Directory.CreateDirectory "state_dump" |> ignore
        IO.File.WriteAllText("state_dump/" + method,
            sprintf "Interpreted method %s (%s) - %s:\n\n%s"  method (String.Join(", ", Seq.map ExprFormat.exprToString args)) name stateDump)
        return result, stateDump
    }

[<Fact>]
let ``Simple XOR method`` () = task {
    let paramA = SParameter.New (CecilTools.intType) "a"
    let paramB = SParameter.New (CecilTools.intType) "b"
    let method = testMethod "A"
    let! result = Interpreter.interpretMethod method state [ SExpr.Parameter paramA; SExpr.Parameter paramB ] dispatcher

    Assert.Equal(result.Stack.Length, 1)
    Assert.Equal("(a ^ b)", ExprFormat.exprToString result.Stack.Head)
}


[<Fact>]
let ``Simple condition`` () = task {
    let paramA = SParameter.New (CecilTools.intType) "a"
    let paramB = SParameter.New (CecilTools.intType) "b"
    let! result1 = Interpreter.interpretMethod (testMethod "WithCondition") state [ SExpr.Parameter paramA; SExpr.Parameter paramB ] dispatcher
    let! result2 = Interpreter.interpretMethod (testMethod "WithCondition2") state [ SExpr.Parameter paramA; SExpr.Parameter paramB ] dispatcher
    // let! result2 = Interpreter.interpretMethod method state [ SExpr.Parameter paramA; SExpr.Parameter paramB ] dispatcher

    // TODO: make these results equal - learn Expression simplifier that `if not c then b else a` <=> `if c then a else b`
    let fresult1 = result1.Stack |> Seq.exactlyOne |> ExprFormat.exprToString
    Assert.Contains("(a + 1)", fresult1)
    Assert.Contains("if ", fresult1)
    let fresult2 = result2.Stack |> Seq.exactlyOne |> ExprFormat.exprToString
    Assert.Contains("(a + 1)", fresult2)
    Assert.Contains("if ", fresult2)
}


[<Fact>]
let ``Simple side effects`` () = task {
    let paramX = SParameter.New (CecilTools.intType) "x"
    let paramY = SParameter.New (CecilTools.convertType typeof<string>) "y"
    let! result1, formatted = interpretMethod "WithSideEffects" "general" state [ SExpr.Parameter paramX; SExpr.Parameter paramY ]
    // let! result2 = Interpreter.interpretMethod method state [ SExpr.Parameter paramA; SExpr.Parameter paramB ] dispatcher

    Assert.Contains("Cisint.Tests.TestInputs.Something::SideEffect2", formatted)
    Assert.Contains("Cisint.Tests.TestInputs.Something::SideEffect1", formatted)
    Assert.Contains("(x * 2)", formatted)
    Assert.Contains("if ", formatted)
    Assert.Equal(1, result1.Stack.Length)
}

[<Fact>]
let ``Simple heap operations - CreateSomeObject`` () = task {
    let paramX = SParameter.New (CecilTools.intType) "x"
    let paramY = SParameter.New (CecilTools.convertType typeof<string>) "y"
    let! result1, formatted = interpretMethod "CreateSomeObject" "general" state [ SExpr.Parameter paramX; SExpr.Parameter paramY ]
    // let! result2 = Interpreter.interpretMethod method state [ SExpr.Parameter paramA; SExpr.Parameter paramB ] dispatcher
    ()
}

[<Fact>]
let ``Simple heap operations - CreateAndUseTheObject`` () = task {
    let paramX = SParameter.New (CecilTools.intType) "x"
    let! result1, formatted = interpretMethod "CreateAndUseTheObject" "general" state [ SExpr.Parameter paramX ]
    // let! result2 = Interpreter.interpretMethod method state [ SExpr.Parameter paramA; SExpr.Parameter paramB ] dispatcher
    ()
}

[<Fact>]
let ``Simple generic test - UseSomeGenerics`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<string>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<string>) "b"
    let! result1, formatted = interpretMethod "UseSomeGenerics" "general" state [ SExpr.Parameter paramA; SExpr.Parameter paramB ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapStuff", formatted)
    ()
}