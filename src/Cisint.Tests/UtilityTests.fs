module UtilityTests
open Xunit
open Cisint.Tests.TestInputs

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
let ``array forall`` () =
    let a1 = [0; 2; 4; 6] |> IArray.ofSeq
    Assert.True(IArray.forall (fun a -> a % 2 = 0) a1)
    Assert.False(IArray.forall (fun a -> a < 0) a1)
    Assert.False(IArray.forall (fun a -> a > 0) a1)
    Assert.False(IArray.forall (fun a -> a < 6) a1)