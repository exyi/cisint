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
open System.Collections.Generic
open CecilTools
let testMethod =
    let t = (CecilTools.convertType typeof<Something>)
    fun name -> t.Definition.Methods |> Seq.find (fun m -> m.Name = name) |> MethodRef

let state = ExecutionState.Empty
let dispatcher = Interpreter.createSynchronousDispatcher (fun frames ->
    // printfn "%A" frames
    if frames.Length > 30 then
        assertOrComplicated false (sprintf "Too many method calls:\n%s" (String.Join("\n", frames |> Seq.map (fun f -> "\t" + f.Method.ToString()))))
    )

printfn "Current directory is %s" (IO.Directory.GetCurrentDirectory())

let interpretMethod method name state args =
    task {
        let methodRef = (testMethod method)
        let! result = Interpreter.interpretMethod methodRef state args dispatcher
        let result = { result with Stack = List.map (fun a -> stackConvert a methodRef.ReturnType |> ExprSimplifier.simplify (AssumptionSet.add [SExpr.ImmConstant true] state.Assumptions)) result.Stack }
        let stateDump = ExprFormat.dumpState result
        IO.Directory.CreateDirectory "state_dump" |> ignore
        IO.File.WriteAllText("state_dump/" + method + "-" + name,
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
    // waitForDebug()
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
    Assert.Equal(
        SExpr.ImmConstant true,
        result1.Stack.Head
    )
}


[<Fact>]
let ``Simple int array - UseSomeArrays`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    let! result1, formatted = interpretMethod "UseSomeArrays" "general" state [ SExpr.Parameter paramA; SExpr.Parameter paramB ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapStuff", formatted)
    Assert.Equal("if (a = b) {\n\t42\n} else {\n\t(b + 1)\n}", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}

[<Fact>]
let ``Simple int array constants - UseSomeArrays`` () = task {
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    let! result1, formatted = interpretMethod "UseSomeArrays" "constant_a" state [ SExpr.ImmConstant 2; SExpr.Parameter paramB ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapStuff", formatted)
    Assert.Equal("if (b = 2) {\n\t42\n} else {\n\t(b + 1)\n}", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}

[<Fact>]
let ``Simple enum processing - UseEnums`` () = task {
    let paramB = SParameter.New (CecilTools.convertType typeof<InstructionFunction>) "b"
    let! result1, formatted = interpretMethod "UseEnums" "constant_a" state [ SExpr.ImmConstant 2; SExpr.Parameter paramB ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapStuff", formatted)
    // Assert.Equal("if (b = 2) {\n\t42\n} else {\n\t(b + 1)\n}", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}

[<Fact>]
let ``Simple devirtualization - IntegerVirtualCall`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let! result1, formatted = interpretMethod "IntegerVirtualCall" "generic" state [ SExpr.Parameter paramA ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapStuff", formatted)
    Assert.Equal("0", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}

[<Fact>]
let ``Simple object processing - UseGenericUnion`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let! result1, formatted = interpretMethod "UseGenericUnion" "generic" state [ SExpr.Parameter paramA ]
    // TODO: execute static constructors
    // Assert.Equal(0, result1.SideEffects.Count)
    // Assert.DoesNotContain(".heapStuff", formatted)
    // Assert.Equal("if (b = 2) {\n\t42\n} else {\n\t(b + 1)\n}", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
    ()
}

[<Fact>]
let ``SimpleTryFinally`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let! result1, formatted = interpretMethod "SimpleTryFinally" "general" state [ SExpr.Parameter paramA ]
    Assert.Equal(1, result1.SideEffects.Count)
    let (c, SideEffect.MethodCall (m, _, args, _virt, _global, _state)) = result1.SideEffects.[0]
    Assert.Equal("true", ExprFormat.exprToString c)
    Assert.Equal("a", ExprFormat.exprToString args.[0])
    Assert.Equal("SideEffect1", m.Reference.Name)
    ()
}

[<Fact>]
let ``csharp iterator - LookAtIterator`` () = task {
    let! result1, formatted = interpretMethod "LookAtIterator" "constant" state [ SExpr.ImmConstant 10 ]
    // TODO: remove dangling side-effects
    Assert.Equal(sprintf "%d" (Something.LookAtIterator 10), List.exactlyOne result1.Stack |> ExprFormat.exprToString)
    ()
}

[<Fact>]
let ``csharp iterator - SumIterator`` () = task {
    let! result1, formatted = interpretMethod "SumIterator" "constant" state [ SExpr.ImmConstant 3 ]
    Assert.Equal("-97", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
    // TODO: remove these side-effects
    // Assert.Equal(0, result1.SideEffects.Count)
    // Assert.DoesNotContain(".heapStuff", formatted)
    ()
}

[<Fact(Skip = "needs static initialized properties")>]
let ``fsharp iterator - MoreComplexIterator`` () = task {
    let! result1, formatted = interpretMethod "MoreComplexIterator" "constant" state [ SExpr.ImmConstant 3 ]
    Assert.Equal(sprintf "%d" (Something.MoreComplexIterator 10), List.exactlyOne result1.Stack |> ExprFormat.exprToString)
    // TODO: remove these side-effects
    // Assert.Equal(0, result1.SideEffects.Count)
    // Assert.DoesNotContain(".heapStuff", formatted)
    ()
}


[<Fact>]
let ``hash table constant - UseHashTable`` () = task {
    let! result1, formatted = interpretMethod "UseHashTable" "constant_a" state [ SExpr.ImmConstant 2 ]
    // Assert.Equal(0, result1.SideEffects.Count)
    // Assert.DoesNotContain(".heapStuff", formatted)
    // Assert.Equal("\"lol\"", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
    ()
}