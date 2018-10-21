module InterpreterTests

open Cisint.Core
open Expression
open System
open Xunit
open InterpreterState
open Cisint.Tests.TestInputs
open FSharp.Control.Tasks.V2
open TypesystemDefinitions
open StateProcessing
let testMethod =
    let t = (CecilTools.convertType typeof<Something>)
    fun name -> t.Definition.Methods |> Seq.find (fun m -> m.Name = name) |> MethodRef

let state = ExecutionState.Empty
let dispatcher = Interpreter.createSynchronousDispatcher (fun frames ->
    // printfn "%A" frames
    if frames.Length > 30 then
        assertOrComplicated false (sprintf "Too many method calls:\n%s" (String.Join("\n", frames |> Seq.map (fun f -> "\t" + f.Method.ToString()))))
    )

let execService =
    { Interpreter.defaultServices with
        Dispatch = dispatcher
        AccessStaticField = Interpreter.aBitSmartReadStaticField
    }
    |> Reimplementations.Dictionary.reimplementDictionary

printfn "Current directory is %s" (IO.Directory.GetCurrentDirectory())

let interpretMethod method name state args =
    task {
        let methodRef = (testMethod method)
        let! result = Interpreter.interpretMethod methodRef state (IArray.ofSeq args) execService
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
    let! result = Interpreter.interpretMethod method state (IArray.ofSeq [ SExpr.Parameter paramA; SExpr.Parameter paramB ]) execService

    Assert.Equal(result.Stack.Length, 1)
    Assert.Equal("(a ^ b)", ExprFormat.exprToString result.Stack.Head)
}


[<Fact>]
let ``Simple condition`` () = task {
    let paramA = SParameter.New (CecilTools.intType) "a"
    let paramB = SParameter.New (CecilTools.intType) "b"
    let! result1 = Interpreter.interpretMethod (testMethod "WithCondition") state (IArray.ofSeq [ SExpr.Parameter paramA; SExpr.Parameter paramB ]) execService
    let! result2 = Interpreter.interpretMethod (testMethod "WithCondition2") state (IArray.ofSeq [ SExpr.Parameter paramA; SExpr.Parameter paramB ]) execService
    // let! result2 = Interpreter.interpretMethod method state [ SExpr.Parameter paramA; SExpr.Parameter paramB ] dispatcher

    // TODO: make these results equal - learn Expression simplifier that `if not c then b else a` <=> `if c then a else b`
    let fresult1 = result1.Stack |> Seq.exactlyOne |> ExprFormat.exprToString
    Assert.Contains("(a + 1)", fresult1)
    Assert.Contains("if ", fresult1)
    let fresult2 = result2.Stack |> Seq.exactlyOne |> ExprFormat.exprToString
    Assert.Contains("(a + 1)", fresult2)
    Assert.Contains("if ", fresult2)
    Assert.Equal (fresult1, fresult2)
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
    Assert.DoesNotContain(".heapState", formatted)
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
    Assert.DoesNotContain(".heapState", formatted)
    Assert.Equal("if (a = b) {\n\t42\n} else {\n\t(b + 1)\n}", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}

[<Fact>]
let ``Simple int array constants - UseSomeArrays`` () = task {
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    let! result1, formatted = interpretMethod "UseSomeArrays" "constant_a" state [ SExpr.ImmConstant 2; SExpr.Parameter paramB ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapState", formatted)
    Assert.Equal("if (b = 2) {\n\t42\n} else {\n\t(b + 1)\n}", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}

[<Fact>]
let ``Simple enum processing - UseEnums`` () = task {
    let paramB = SParameter.New (CecilTools.convertType typeof<InstructionFunction>) "b"
    let! result1, formatted = interpretMethod "UseEnums" "constant_a" state [ SExpr.ImmConstant 2; SExpr.Parameter paramB ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapState", formatted)
    // Assert.Equal("if (b = 2) {\n\t42\n} else {\n\t(b + 1)\n}", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}

[<Fact>]
let ``Simple devirtualization - IntegerVirtualCall`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let! result1, formatted = interpretMethod "IntegerVirtualCall" "generic" state [ SExpr.Parameter paramA ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapState", formatted)
    Assert.Equal("0", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}

[<Fact>]
let ``Simple object processing - UseGenericUnion`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let! result1, formatted = interpretMethod "UseGenericUnion" "generic" state [ SExpr.Parameter paramA ]
    // TODO: execute static constructors
    // Assert.Equal(0, result1.SideEffects.Count)
    // Assert.DoesNotContain(".heapState", formatted)
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
    // Assert.DoesNotContain(".heapState", formatted)
    ()
}

[<Fact()>]
let ``fsharp simple iterator contant - FsharpIterator`` () = task {
    let! result1, formatted = interpretMethod "FsharpIterator" "constant" state [ SExpr.ImmConstant 3 ]
    Assert.Equal(sprintf "%d" (Something.FsharpIterator 3), List.exactlyOne result1.Stack |> ExprFormat.exprToString)
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapState", formatted)
    ()
}

[<Fact()>]
let ``fsharp simple iterator - FsharpIterator`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let! result1, formatted = interpretMethod "FsharpIterator" "general" state [ SExpr.Parameter paramA ]
    Assert.Equal(SExpr.Parameter paramA, List.exactlyOne result1.Stack)
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.DoesNotContain(".heapState", formatted)
    ()
}

[<Fact()>]
let ``fsharp iterator - MoreComplexIterator`` () = task {
    let! result1, formatted = interpretMethod "MoreComplexIterator" "constant" state [ SExpr.ImmConstant 10 ]
    Assert.Equal(sprintf "%d" (Something.MoreComplexIterator 10), List.exactlyOne result1.Stack |> ExprFormat.exprToString)
    // TODO: remove these side-effects
    // Assert.Equal(0, result1.SideEffects.Count)
    // Assert.DoesNotContain(".heapState", formatted)
    ()
}

[<Fact>]
let ``create object - ReturnObject`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let! result1, formatted = interpretMethod "ReturnObject" "generic" state [ SExpr.Parameter paramA ]
    let resultP = result1.ChangedHeapObjects |> List.head
    Assert.Equal("""
                .heapState {
                    let o154 = new System.Tuple`2<System.Int32,System.Int32>
                    o154.m_Item1 = a
                    o154.m_Item2 = (a + 1)
                }

                return [
                    o154
                ]
                 """.Replace("o154", resultP.Name) |> removeWhitespace, removeWhitespace formatted)
}

[<Fact>]
let ``do stuff with object - DoStuffWithTuple`` () = task {
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let! result1, formatted = interpretMethod "DoStuffWithTuple" "generic" state [ SExpr.Parameter paramA ]
    Assert.Equal(removeWhitespace "return [(a + (a + 1))]", removeWhitespace formatted)
}

[<Fact>]
let ``iterators and lambdas - FSharpLambdasAndSeq`` () = task {
    let! result1, formatted = interpretMethod "FSharpLambdasAndSeq" "constant_a" state [ SExpr.ImmConstant 1 ]
    Assert.Equal(sprintf "%d" (Something.FSharpLambdasAndSeq 1), List.exactlyOne result1.Stack |> ExprFormat.exprToString)
}


[<Fact>]
let ``hash table constant - UseHashTable`` () = task {
    let! result1, formatted1 = interpretMethod "UseHashTable" "constant_a" state [ SExpr.ImmConstant 2 ]
    let! result2, formatted2 = interpretMethod "UseHashTable" "constant_b" state [ SExpr.ImmConstant 43 ]
    Assert.Equal(0, result1.SideEffects.Count)
    Assert.Equal(0, result2.SideEffects.Count)
    Assert.DoesNotContain(".heapState", formatted1)
    Assert.DoesNotContain(".heapState", formatted2)
    Assert.Equal("\"lol\"", List.exactlyOne result1.Stack |> ExprFormat.exprToString)
    Assert.Equal("\"a\"", List.exactlyOne result2.Stack |> ExprFormat.exprToString)
    ()
}