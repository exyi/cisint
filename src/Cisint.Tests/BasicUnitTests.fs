module BasicUnitTests

open Cisint.Core
open Expression
open System
open Xunit
open System.Collections.Generic
open InterpreterState
open Cisint.Tests.TestInputs
open TypesystemDefinitions

[<Fact>]
let ``Cecil smoke test`` () =
    let testType : Type = typeof<Cisint.Tests.TestInputs.Something>
    let containsXOR = Intro.methodContainsXOR testType.Assembly.Location testType.FullName "A"
    Assert.True containsXOR

[<Fact>]
let ``Test input`` () =
    let testType = typeof<Cisint.Tests.TestInputs.Something> |> CecilTools.convertType
    let m = testType.Definition.Methods |> Seq.find (fun m -> m.Name = "WithExceptionHandler")
    Assert.True(m.Body.HasExceptionHandlers)
    Assert.Equal(1, m.Body.ExceptionHandlers.Count)
    // m.Body.Instructions |> Seq.iter (printfn "%O")
    // m.Body.ExceptionHandlers |> Seq.iter (printfn "%O")

[<Fact>]
let ``expression comparison`` () =
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    Assert.True(paramA.Type = paramB.Type, "same types are not equal")
    Assert.Equal(paramA.Type, paramB.Type)
    Assert.Equal((SExpr.Parameter paramA).Node, (SExpr.Parameter paramA).Node)
    let someParamExpr = SExpr.Parameter paramA
    let someParamNode = (SExpr.Parameter paramA).Node
    Assert.Equal(AssumptionSetVersion.None, AssumptionSetVersion.None)
    Assert.Equal(someParamExpr, someParamExpr)
    Assert.True(AssumptionSetVersion.None = AssumptionSetVersion.None, "wtf, they are not equal for F#")
    Assert.True(Microsoft.FSharp.Core.LanguagePrimitives.HashCompare.GenericEqualityERIntrinsic AssumptionSetVersion.None AssumptionSetVersion.None, "wtf, they are not equal for some magic function?")
    Assert.Equal(
        { SExpr.Node = someParamNode; ResultType = paramA.Type; SimplificationVersion = AssumptionSetVersion.None; NodeRank = 1L; NodeLeavesRank = 0 },
        { SExpr.Node = someParamNode; ResultType = paramA.Type; SimplificationVersion = AssumptionSetVersion.None; NodeRank = 1L; NodeLeavesRank = 0 }
    )
    Assert.True(SExpr.Parameter paramA = SExpr.Parameter paramA, "F# comparison says false")
    Assert.True(EqualityComparer.Default.Equals(SExpr.Parameter paramA, SExpr.Parameter paramA), ".NET comparison says false")
    Assert.Equal(SExpr.Parameter paramA, SExpr.Parameter paramA)
    Assert.Equal(EqArray.OfSeq [ SExpr.Parameter paramA ], EqArray.OfSeq [ SExpr.Parameter paramA ])
    let expr1 () =
        SExpr.InstructionCall
            InstructionFunction.Add
            (CecilTools.convertType typeof<int>)
            [ SExpr.Parameter paramA; SExpr.Parameter paramB ]

    Assert.Equal(expr1(), expr1())

[<Fact>]
let ``ExprSimplifier.createExprFromQuot smoke test`` () =
    let (a, b) = SParameter.New (CecilTools.convertType typeof<int>) "a", SParameter.New (CecilTools.convertType typeof<int>) "b"
    let q = <@ fun a b -> a + -b  @>
    Assert.Equal(
        ExprSimplifier.createExprFromQuot q [a; b],
        SExpr.InstructionCall
            InstructionFunction.Add
            (CecilTools.convertType typeof<int>)
            [
                SExpr.Parameter a
                SExpr.InstructionCall
                    InstructionFunction.Negate
                        (CecilTools.convertType typeof<int>)
                        [ SExpr.Parameter b ]
            ]
    )

[<Fact>]
let ``pattern matching smoke test`` () =
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    let paramC = SParameter.New (CecilTools.convertType typeof<int>) "c"
    let pattern = ExprSimplifier.createExprFromQuot <@ fun (a: int) (b: int) -> Math.Max ((a + b), (a - b)) @> [paramA; paramB]
    let expression = ExprSimplifier.createExprFromQuot <@ fun () -> Math.Max ((3 + 12), (3 - 12)) @> []

    let result = ExprSimplifier.patternMatch expression pattern (IArray.ofSeq [ paramB; paramA; paramC ]) (IArray.ofSeq [])
    Assert.Equal (
        result,
        Ok (IArray.ofSeq [ Some (SExpr.ImmConstant 12); Some (SExpr.ImmConstant 3); None ])
    )

    let expression = ExprSimplifier.createExprFromQuot <@ fun () -> Math.Max ((3 + 12), (3 - 11)) @> []
    let result2 = ExprSimplifier.patternMatch expression pattern (IArray.ofSeq [paramB; paramA; paramC]) (IArray.ofSeq [])
    Assert.Equal (result2, Error ())

[<Fact>]
let ``expression comparison smoke`` () =
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    let paramC = SParameter.New (CecilTools.convertType typeof<int>) "c"
    let e1 = ExprSimplifier.createExprFromQuot <@ fun (a: int) (b: int) (c: int) -> ((a + b) + c) @> [paramA; paramB; paramC]
    let e1_b = ExprSimplifier.createExprFromQuot <@ fun (a: int) (b: int) (c: int) -> ((a + b) + c) @> [paramA; paramB; paramC]
    let e2 = ExprSimplifier.createExprFromQuot <@ fun (a: int) (b: int) -> Math.Max ((3 + 12), (3 - 11)) @> [paramA; paramB; paramC]
    let e_const = ExprSimplifier.createExprFromQuot <@ fun (a: int) (b: int) (c: int) -> 3 @> [paramA; paramB; paramC]

    Assert.Equal(
        ExprCompare.exprCompare e_const e1,
        -1
    )
    Assert.Equal(
        ExprCompare.exprCompare e_const e2,
        -1
    )
    Assert.Equal(
        ExprCompare.exprCompare e1 e_const,
        1
    )
    Assert.Equal(
        ExprCompare.exprCompare e1_b e1,
        0
    )
    Assert.NotEqual(
        ExprCompare.exprCompare e2 e1,
        0
    )

let basePatterns = [
        ExprSimplifier.createPatternFromQuot
            [ typeof<int>; typeof<int>; typeof<int> ]
            [ <@ fun a b c -> (a + b) + c @>; <@ fun a b c -> a + (c + b) @> ]
        ExprSimplifier.createPatternFromQuot
            [ typeof<int>; typeof<int>; typeof<int> ]
            [ <@ fun a b c -> (a - b) + c + b @>; <@ fun a b c -> a + c @> ]
        ExprSimplifier.createPatternFromQuot
            [ typeof<int>; typeof<int> ]
            [ <@ fun a b -> (a + b) @>; <@ fun a b -> (b + a) @> ]
        ExprSimplifier.createPatternFromQuot
            [ typeof<int> ]
            [ <@ fun a -> (a + 0) @>; <@ fun a -> a @> ]
        ExprSimplifier.createPatternFromQuot
            [ typeof<int>; typeof<int> ]
            [ <@ fun a b -> a - b @>; <@ fun a b -> a + (-b) @> ]
        ExprSimplifier.createPatternFromQuot
            [ typeof<int> ]
            [ <@ fun a -> a - a @>; <@ fun a -> 0 @> ]
    ]

[<Fact>]
let ``simplifier map smoke test`` () =
    let derivedPatterns = ExprSimplifier.extendPatterns basePatterns
    let exprs = seq {
                    for i in derivedPatterns do
                    // printfn "\n## pattern with vars %s" (String.Join(", ", i.Variables |> Seq.map (fun t -> t.Name)))
                    for j in i.EqExpressions do
                        let l = sprintf "%s" (ExprFormat.exprToString j)
                        // printfn "%s" (l |> ExprFormat.tabRight)
                        yield l
                } |> Set.ofSeq
    Assert.True(Set.contains "(p0 + 0)" exprs)
    Assert.True(Set.contains "p0" exprs)
    Assert.True(Set.contains "(p2 + (p0 + p1))" exprs)
    Assert.True(Set.contains "0" exprs)
    Assert.True(Set.contains "(p0 + -p0)" exprs)

[<Fact>]
let ``simplifier smoke test`` () =
    let simplifier = ExprSimplifier.createSimplifier basePatterns
    let emptyAS = AssumptionSet.empty
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    let paramC = SParameter.New (CecilTools.convertType typeof<int>) "c"
    let expr1 = ExprSimplifier.createExprFromQuot <@ fun a b -> a + b @> [paramA; paramB]
    let expr2 = ExprSimplifier.createExprFromQuot <@ fun a b -> b + a @> [paramA; paramB]

    Assert.Equal(
        ExprFormat.exprToString (simplifier emptyAS expr1),
        ExprFormat.exprToString (simplifier emptyAS expr2))
    let expr3 = ExprSimplifier.createExprFromQuot <@ fun a b -> b + (a - b) - a @> [paramA; paramB]
    Assert.Equal("0", (ExprFormat.exprToString (simplifier emptyAS expr3)))
    Assert.Equal(
        simplifier emptyAS expr1,
        simplifier emptyAS expr2
    )

[<Fact>]
let ``simplifier constant collection test`` () =
    let simplifier = ExprSimplifier.createSimplifier basePatterns
    let emptyAS = AssumptionSet.empty
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    let expr1 = ExprSimplifier.createExprFromQuot <@ fun a b -> a + 1 + b + 23 @> [paramA; paramB]
    let expr2 = ExprSimplifier.createExprFromQuot <@ fun a b -> b + a + 23 + 1 @> [paramA; paramB]

    Assert.Contains(
        "24",
        ExprFormat.exprToString (simplifier emptyAS expr1)
    )
    Assert.Equal(
        simplifier emptyAS expr1,
        simplifier emptyAS expr2
    )

[<Fact>]
let ``default simplifier conditions`` () =
    let emptyAS = AssumptionSet.empty
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    let expr1 = ExprSimplifier.createExprFromQuot <@ fun a b -> if a < b then a else b @> [paramA; paramB]
    let expr2 = ExprSimplifier.createExprFromQuot <@ fun a b -> if not (a < b) then b else a @> [paramA; paramB]

    // printfn "%s" (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr1))
    // printfn "%s" (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr2))
    Assert.Equal(
        ExprSimplifier.simplify emptyAS expr1,
        ExprSimplifier.simplify emptyAS expr2
    )

[<Fact>]
let ``simplifier - type checks on Int32`` () =
    let emptyAS = AssumptionSet.empty
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let expr1 = ExprSimplifier.createExprFromQuot <@ fun a -> (box a) :? System.Collections.IEnumerable @> [paramA]
    let expr2 = ExprSimplifier.createExprFromQuot <@ fun a -> (box a) :? System.IComparable @> [paramA]
    let expr3 = ExprSimplifier.createExprFromQuot <@ fun a -> (box a) :? System.Int32 @> [paramA]
    let expr4 = ExprSimplifier.createExprFromQuot <@ fun a -> (box a) :? System.Int64 @> [paramA]
    let expr5 = ExprSimplifier.createExprFromQuot <@ fun a -> (box a) :? System.Array @> [paramA]
    let expr6 = ExprSimplifier.createExprFromQuot <@ fun a -> ((box a) :?> System.IComparable) :? System.IFormattable @> [paramA]
    let expr7 = ExprSimplifier.createExprFromQuot <@ fun a -> (castAs<System.Collections.IEnumerable>((box a))) :?> System.Object = null @> [paramA]

    // printfn "expr1: %s -> %s" (ExprFormat.exprToString expr1) (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr1))
    // printfn "expr2: %s -> %s" (ExprFormat.exprToString expr2) (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr2))
    // printfn "expr3: %s -> %s" (ExprFormat.exprToString expr3) (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr3))
    // printfn "expr4: %s -> %s" (ExprFormat.exprToString expr4) (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr4))
    // printfn "expr5: %s -> %s" (ExprFormat.exprToString expr5) (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr5))
    // printfn "expr6: %s -> %s" (ExprFormat.exprToString expr6) (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr6))
    // printfn "expr7: %s -> %s" (ExprFormat.exprToString expr7) (ExprFormat.exprToString (ExprSimplifier.simplify emptyAS expr7))
    Assert.Equal(ExprSimplifier.simplify emptyAS expr1, SExpr.ImmConstant false)
    Assert.Equal(ExprSimplifier.simplify emptyAS expr2, SExpr.ImmConstant true)
    Assert.Equal(ExprSimplifier.simplify emptyAS expr3, SExpr.ImmConstant true)
    Assert.Equal(ExprSimplifier.simplify emptyAS expr4, SExpr.ImmConstant false)
    Assert.Equal(ExprSimplifier.simplify emptyAS expr5, SExpr.ImmConstant false)
    Assert.Equal(ExprSimplifier.simplify emptyAS expr6, SExpr.ImmConstant true)
    Assert.Equal(ExprSimplifier.simplify emptyAS expr7, SExpr.ImmConstant true)

[<Fact>]
let ``basic overload resolution`` () =
    let o = CecilTools.convertType typeof<TestRecord>
    let m = CecilTools.objType.Definition.Methods |> Seq.find (fun m -> m.Name = "GetHashCode") |> MethodRef
    let m2 = StateProcessing.findOverridenMethod o m
    Assert.Equal(o, m2.DeclaringType)

[<Fact>]
let ``generic overload resolution`` () =
    let o =
        let o = CecilTools.convertType typeof<TestRecord>
        let p = o.Definition.Properties |> Seq.find (fun p -> p.Name = "AnotherProp")
        TypeRef p.PropertyType
    Assert.Equal("Microsoft.FSharp.Core.FSharpOption`1<System.String>", o.ToString())
    let m = CecilTools.objType.Definition.Methods |> Seq.find (fun m -> m.Name = "GetHashCode") |> MethodRef
    let m2 = StateProcessing.findOverridenMethod o m
    Assert.Equal(o, m2.DeclaringType)
    Assert.Equal("System.Int32 Microsoft.FSharp.Core.FSharpOption`1<System.String>::GetHashCode()", m2.ToString())

[<Fact>]
let ``not so generic overload resolution`` () =
    let o1 =
        let o = CecilTools.convertType typeof<Something>
        let p = o.Definition.Methods |> Seq.find (fun p -> p.Name = "CreateSomeGenericBazmek")
        TypeRef p.ReturnType
    let o2 = CecilTools.convertType typeof<NotSoGenericType>
    Assert.Equal("Cisint.Tests.TestInputs.GenericVirtType`1<System.String>", o1.ToString())
    let m = (o1.Definition.Methods |> Seq.find (fun m -> m.Name = "Nothing")).RebaseOn(o1.Reference).ResolvePreserve(o1.GenericParameterAssigner) |> MethodRef
    Assert.Equal("System.Boolean Cisint.Tests.TestInputs.GenericVirtType`1<System.String>::Nothing(x)", m.ToString())
    let m2 = StateProcessing.findOverridenMethod o2 m
    Assert.Equal(o2, m2.DeclaringType)
    Assert.Equal("System.Boolean Cisint.Tests.TestInputs.NotSoGenericType::Nothing(System.String)", m2.ToString())

[<Fact>]
let ``devirtualization on interface works`` () =
    let param = SParameter.New (CecilTools.convertType typeof<System.Collections.ICollection>) ""
    let moveNext = (CecilTools.convertType typeof<System.Collections.IEnumerable>).Methods |> Seq.find (fun m -> m.Reference.Name = "GetEnumerator")
    let targets = StateProcessing.devirtualize moveNext (IArray.ofSeq [ SExpr.Cast InstructionFunction.Cast (CecilTools.convertType typeof<Collections.IEnumerable>) (SExpr.Parameter param) ]) ExecutionState.Empty
    Assert.Equal(targets.Length, 1)
    Assert.Equal(targets.[0], (SExpr.ImmConstant true, moveNext, true))
