namespace Cisint.Tests.TestInputs

type Something = class
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