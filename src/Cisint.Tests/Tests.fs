module Tests

open Cisint.Core
open Expression
open System
open Xunit
open System.Collections.Generic
open Expression
open Expression
open System.Collections.Generic

[<Fact>]
let ``Cecil smoke test`` () =
    let tt = struct (1, 2)
    let testType : Type = typeof<Cisint.Tests.TestInputs.Something>
    let containsXOR = Intro.methodContainsXOR testType.Assembly.Location testType.FullName "A"
    Assert.True containsXOR

[<Fact>]
let ``expression comparison`` () =
    let paramA = SParameter.New (CecilTools.convertType typeof<int>) "a"
    let paramB = SParameter.New (CecilTools.convertType typeof<int>) "b"
    Assert.True(Object.ReferenceEquals(paramA.Type, paramB.Type), "same types are not equal")
    Assert.Equal(paramA.Type, paramB.Type)
    Assert.Equal((SExpr.Parameter paramA).Node, (SExpr.Parameter paramA).Node)
    let someParamExpr = SExpr.Parameter paramA
    let someParamNode = (SExpr.Parameter paramA).Node
    Assert.Equal(AssumptionSetVersion.None, AssumptionSetVersion.None)
    Assert.Equal(someParamExpr, someParamExpr)
    Assert.True(AssumptionSetVersion.None = AssumptionSetVersion.None, "wtf, they are not equal for F#")
    Assert.True(Microsoft.FSharp.Core.LanguagePrimitives.HashCompare.GenericEqualityERIntrinsic AssumptionSetVersion.None AssumptionSetVersion.None, "wtf, they are not equal for some magic function?")
    Assert.Equal(
        { SExpr.Node = someParamNode; ResultType = paramA.Type; SimplificationVersion = AssumptionSetVersion.None; NodeCountRank = 1; NodeLeavesRank = 0 },
        { SExpr.Node = someParamNode; ResultType = paramA.Type; SimplificationVersion = AssumptionSetVersion.None; NodeCountRank = 1; NodeLeavesRank = 0 }
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
    // Assert.Equal(
    //     simplifier emptyAS expr1,
    //     expr1
    // )