module UtilityTests
open Xunit
open Cisint.Tests.TestInputs
open Mono.Cecil
open Mono.Cecil.Cil

[<Fact>]
let ``init IArray`` () =
    let a = IArray.init 1 (fun a -> a)
    Assert.Equal(1, a.Length)
    Assert.Equal(0, a.[0])

[<Fact>]
let ``Mono.Cecil inheritance`` () =
    let tI = CecilTools.convertType typeof<TestI>
    let tC = CecilTools.convertType typeof<TestC>
    let tC2 = CecilTools.convertType typeof<TestC2>
    let tC3 = CecilTools.convertType typeof<TestC3>

    Assert.True(
        tC2.Definition.Methods |> Seq.map (sprintf "T2 method: %O") |> Seq.toList =
            [
                "T2 method: System.Int32 Cisint.Tests.TestInputs.TestC2::M()"
                "T2 method: System.Int32 Cisint.Tests.TestInputs.TestC2::Cisint-Tests-TestInputs-TestI-M()"
            ]
    )

[<Fact>]
let ``Mono.Cecil generics`` () =
    let t1 = CecilTools.convertType typeof<GenericType<string>>
    let method1 = t1.Definition.Methods |> Seq.find (fun m -> m.Name = "Contains")
    Assert.Equal("System.Boolean Cisint.Tests.TestInputs.GenericType`1::Contains(x)", method1.FullName)
    Assert.True(method1.ContainsGenericParameter)
    Assert.Equal(MethodCallingConvention.Default, method1.CallingConvention)
    Assert.False(method1.HasGenericParameters)
    Assert.Equal(0, method1.GenericParameters.Count)
    Assert.False(method1.IsVirtual)

    let method2 = t1.Definition.Methods |> Seq.find (fun m -> m.Name = "DoNothing")
    Assert.Equal("a Cisint.Tests.TestInputs.GenericType`1::DoNothing(a)", method2.FullName)
    Assert.True(method2.ContainsGenericParameter)
    Assert.Equal(MethodCallingConvention.Generic, method2.CallingConvention)
    Assert.True(method2.HasGenericParameters)
    Assert.Equal(1, method2.GenericParameters.Count)
    Assert.Equal("a", method2.GenericParameters.[0].FullName)
    Assert.True(method2.GenericParameters.[0].IsGenericParameter)
    Assert.False(method2.IsVirtual)

    let method3 = t1.Definition.Methods |> Seq.find (fun m -> m.Name = "ProcWithNothing")
    let callInstruction = method3.Body.Instructions |> Seq.find (fun i -> i.OpCode.OperandType = OperandType.InlineMethod)
    let calledMethod = callInstruction.Operand :?> MethodReference
    let calledMethodResolved = calledMethod.ResolvePreserve()
    Assert.Equal("!!0 Cisint.Tests.TestInputs.GenericType`1<x>::DoNothing<x>(!!0)", calledMethod.FullName)
    Assert.False(calledMethod.HasGenericParameters)
    Assert.Equal("!!0 Cisint.Tests.TestInputs.GenericType`1<x>::DoNothing<x>(!!0)", calledMethodResolved.FullName)
    Assert.True(calledMethodResolved.DeclaringType.GetElementType().IsDefinition)
    Assert.False(calledMethod.HasGenericParameters)

[<Fact>]
let ``array forall`` () =
    let a1 = [0; 2; 4; 6] |> IArray.ofSeq
    Assert.True(IArray.forall (fun a -> a % 2 = 0) a1)
    Assert.False(IArray.forall (fun a -> a < 0) a1)
    Assert.False(IArray.forall (fun a -> a > 0) a1)
    Assert.False(IArray.forall (fun a -> a < 6) a1)