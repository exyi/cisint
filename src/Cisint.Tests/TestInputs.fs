namespace Cisint.Tests.TestInputs

open Expression
open System.Collections.Generic
type TestRecord = {
    SomeProp: int
    AnotherProp: string Option
} with
    static member Create count =
        { TestRecord.SomeProp = count; AnotherProp = None }
    member x.WithStr t =
        { x with AnotherProp = Some t }

type GenericType<'x> when 'x : not struct = {
    Something: 'x
} with
    member x.Contains b = LanguagePrimitives.PhysicalEquality x.Something b
    member x.DoNothing d = d
    member x.ProcWithNothing () = x.DoNothing x.Something

type GenericUnion<'x> =
    | One of 'x
    | Two of 'x * 'x
with
    static member Double a = Two(a, a)

type GenericVirtType<'x>() =
    abstract member Nothing : 'x -> bool
    default x.Nothing a = true

type NotSoGenericType() =
    inherit GenericVirtType<string>()
    override x.Nothing (a: string) = a.Contains "a"


type Something = class
    static member GetSomeDictionary (i: int) = let d = Dictionary<string, int>()
                                               d.Add("i", i)
                                               d
    static member A a b = a ^^^ b
    static member WithCondition a b = if a + 1 > b then a + 1 else b
    static member WithCondition2 a b = if a + 1 <= b then b else a + 1
    static member WithExceptionHandler a =
        try
            System.Int32.Parse(a)
        with ex ->
            System.Console.WriteLine ex
            0

    static member SideEffect1 a =
        while true do ()
        (a + 1).ToString()
    static member SideEffect2 (a: string) =
        while true do ()
        a.Length

    static member WithSideEffects x y =
        if Something.SideEffect2 y > 4 then
            Something.SideEffect1 x
        else
            Something.SideEffect1 (x * 2)

    static member CreateSomeObject x y =
        (TestRecord.Create x).WithStr y

    static member CreateAndUseTheObject a =
        (Something.CreateSomeObject a "1").GetHashCode()

    static member UseSomeGenerics (a:string) (b: string) =
        let a = { Something = a }
        a.Contains (a.ProcWithNothing ()) || a.Contains b

    static member CreateSomeGenericBazmek () =
        NotSoGenericType() :> GenericVirtType<string>

    static member UseSomeArrays (a: int) (b: int) =
        let array = [|b; b; b|]
        array.[a] <- b + 1
        array.[b] <- 42
        if array.Length <> 3 then
            Something.SideEffect1 1 |> ignore
        // if array.LongLength <> 3L then // TODO: add instristic for this
        //     Something.SideEffect1 1 |> ignore
        array.[a]

    static member UseEnums (a: int) (b: InstructionFunction) =
        LanguagePrimitives.EnumToValue b = a ||
            LanguagePrimitives.EnumToValue b = 3 ||
            LanguagePrimitives.EnumToValue b = LanguagePrimitives.EnumToValue System.DateTimeKind.Utc ||
            LanguagePrimitives.EnumOfValue 4 = b ||
            LanguagePrimitives.EnumOfValue 6432 = b
    static member IntegerVirtualCall (a: int) =
        let eq = a :> System.IComparable
        if eq :? System.Collections.IEnumerable then
            Something.SideEffect1 1 |> ignore
        if eq :? System.Array then
            Something.SideEffect1 2 |> ignore
        eq.CompareTo(box a)
    static member UseGenericUnion (a: int) =
        match GenericUnion<int>.Double a with
        | Two (x, y) as a -> x + y, a.GetHashCode()
        | One x -> x, 1

    static member UseHashTable (a: int) =
        let h = System.Collections.Generic.Dictionary()
        h.Add(43, "a")
        h.Add(76543, "b")
        h.Add(5355, "c")
        match h.TryGetValue(a) with
        | (true, a) -> a
        | _ -> "lol"

    static member SimpleTryFinally (a: int) =
        try
            Something.SideEffect1 a
        finally
            Something.WithCondition a (a + 1) |> ignore

    static member SumIterator (a: int) =
        Cisint.CsharpTestInputs.Class1.YieldSomeInts a |> Seq.sum
end




type TestI =
    abstract member M: unit -> int
type TestC =
    abstract member M: unit -> int
    default x.M() = 1
    abstract member M2: unit -> int
    default x.M2() = -1
    interface TestI with
        member x.M() = 2
type TestC2 =
    inherit TestC
    override x.M() = 3
    interface TestI with
        member x.M() = 4
type TestC3 =
    inherit TestC2
    override x.M() = 5
    override x.M2() = -5