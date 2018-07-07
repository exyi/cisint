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

    static member SideEffect1 a = string (a + 1)
    static member SideEffect2 (a: string) = a.Length

    static member WithSideEffects x y =
        if Something.SideEffect2 y > 4 then
            Something.SideEffect1 x
        else
            Something.SideEffect1 (x * 2)

end