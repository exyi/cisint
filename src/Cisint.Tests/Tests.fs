module Tests

open Cisint.Core
open System
open Xunit

[<Fact>]
let ``My test`` () =
    let testType : Type = typeof<Cisint.Tests.TestInputs.Something>
    let containsXOR = Intro.methodContainsXOR testType.Assembly.Location testType.FullName "A"
    Assert.True containsXOR
