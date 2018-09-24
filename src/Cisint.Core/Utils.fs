[<AutoOpen>]
module Utils
open System.Collections.Immutable
open System
open System.Collections.Generic
open Mono.Cecil
open Mono.Cecil
open Mono.Cecil
open Mono.Cecil


let waitForDebug () =
#if DEBUG
    if not(System.Diagnostics.Debugger.IsAttached) then
        printfn "Please attach a debugger, PID = %d" (System.Diagnostics.Process.GetCurrentProcess().Id)
        while not(System.Diagnostics.Debugger.IsAttached) do
            System.Threading.Thread.Sleep(100)
        System.Diagnostics.Debugger.Break()
#endif
    ()

let softAssert condition message =
    if not condition then
        #if DEBUG
        if System.Environment.GetEnvironmentVariable "DEBUG" |> String.IsNullOrEmpty then
            failwithf "Assertion failed: %s" message
        else
            let b = Console.ForegroundColor
            Console.ForegroundColor <- ConsoleColor.Red
            printfn "Assertion failed: %s" message
            printfn "Do you want to [c]ontinue, [d]ebug or [t]hrow?"
            Console.ForegroundColor <- b
            match Console.ReadKey(true).KeyChar with
            | 'c' -> ()
            | 'd' -> waitForDebug ()
            | _ ->
        #endif
                failwithf "Assertion failed: %s" message

type clist<'a> = list<'a>
type array<'a> = ImmutableArray<'a>
type list<'a> = ImmutableList<'a>
type dict<'a, 'b> = ImmutableDictionary<'a, 'b>

[<Struct>]
[<CustomEquality>] [<NoComparison>]
/// ImmutableArray with correct value-comparison
type EqArray<'a> = {
    arr: array<'a>
}
with
        member a.Equals b = Object.ReferenceEquals(a.arr, b.arr) || (a.arr.Length = b.arr.Length && Linq.Enumerable.SequenceEqual(a.arr, b.arr))
        interface IEquatable<EqArray<'a>> with
            member a.Equals b = a.Equals b
        override a.Equals b =
            // if System.DateTime.Now.Minute > 26 then
            //     waitForDebug()
            match b with
            | :? EqArray<'a> as b -> a.Equals b
            | _ -> false
        override a.GetHashCode() =
            // PERF: specialize fold
            a.arr.Length * 319 + Seq.fold (fun s x -> (s * 19) + EqualityComparer.Default.GetHashCode x) 87654567 a.arr

module EqArray =
        let New arr = { EqArray.arr = arr }
        let OfSeq (s: #seq<_>) = New (ImmutableArray.CreateRange s)
        let inline (|AP|) arr =
            List.ofSeq arr.arr

module IArray =
    // PERF: maybe these should inline
    let map f (arr: 'a array) =
        let b = ImmutableArray.CreateBuilder(arr.Length)
        for i in arr do
            b.Add(f i)
        b.MoveToImmutable()
    let mapi f (arr: 'a array) =
        let b = ImmutableArray.CreateBuilder(arr.Length)
        for i = 0 to arr.Length - 1 do
            b.Add(f i arr.[i])
        b.MoveToImmutable()
    let collect (f: 'a -> #seq<'b>) (arr: 'a array) =
        let b = ImmutableArray.CreateBuilder()
        for i in arr do
            b.AddRange(f i :> seq<'b>)
        b.ToImmutable()
    let choose (f : 'a -> option<'b>) (arr: 'a array) =
        let b = ImmutableArray.CreateBuilder()
        for i in arr do
            match f i with
            | Some x -> b.Add(x)
            | None -> ()
        b.ToImmutable()
    let filter (f : 'a -> bool) (arr: 'a array) =
        let b = ImmutableArray.CreateBuilder()
        for i in arr do
            if f i then
                b.Add i
        b.ToImmutable()
    let init count gen =
        let b = ImmutableArray.CreateBuilder(count)
        for i = 0 to (count - 1) do
            b.Add(gen i)
        b.MoveToImmutable()

    let forall fn (array:'a array) =
        let mutable i = 0
        while i < array.Length && fn array.[i] do
            i <- i + 1
        i = array.Length
    let append (a: 'a array) (b: 'a array) =
        a.AddRange(b)
    let ofSeq (a: #seq<'a>) = ImmutableArray.CreateRange a

type ImmutableDictionary<'key, 'value> with
    member x.TryGet key =
        match x.TryGetValue key with
        | (true, a) -> Some a
        | (false, _) -> None

// module SeqPlus =
//   let inline exactlyOneDistinct (arr: 'a seq) =
//     if arr.Length = 0 then None
//     else
//       let f = arr |>
//       for i in arr do
//         if

type internal Marker = interface end

let castAs<'T when 'T : null> (o:obj) =
    match o with
    | :? 'T as res -> res
    | _ -> null

let justAnd a b = a && b
let justOr a b = a || b

let getOnlyElement (xs: #seq<'a>) =
    let mutable result = None
    if xs |> Seq.forall (fun x -> if result.IsNone then result <- Some x; true
                                  else LanguagePrimitives.PhysicalEquality result.Value x || result.Value = x) then
        result
    else
        None

let optionExpect msg = function None -> failwithf "Option expectation failed: %s" msg | Some x -> x

type TypeReference with
        member x.TryResolve() =
                let a = x.Resolve()
                if isNull a then x else a :> TypeReference
        member x.ResolvePreserve () = x.ResolvePreserve(fun _ -> None)
        member x.ResolvePreserve (customMapping: TypeReference -> TypeReference option) : TypeReference =
                let mapping = customMapping x
                if mapping.IsSome then
                    mapping.Value
                elif x.IsGenericInstance then
                    let previousInstance = x :?> GenericInstanceType
                    let instance = new GenericInstanceType(previousInstance.ElementType.ResolvePreserve(fun m ->
                        // blacklist the parameters
                        if m :? GenericParameter && previousInstance.ElementType.GenericParameters.Contains (m :?> GenericParameter) then
                            None
                        else customMapping m))
                    for argument in previousInstance.GenericArguments do
                        instance.GenericArguments.Add (argument.ResolvePreserve(customMapping))
                    instance :> TypeReference
                elif x.IsArray then
                    let x = x :?> ArrayType
                    new Mono.Cecil.ArrayType(x.ElementType.ResolvePreserve(customMapping), x.Rank) :> TypeReference

                elif x.IsByReference then
                    let x = x :?> ByReferenceType
                    new Mono.Cecil.ByReferenceType(x.ElementType.ResolvePreserve(customMapping)) :> TypeReference
                elif x.IsPointer then
                    let x = x :?> PointerType
                    new Mono.Cecil.PointerType(x.ElementType.ResolvePreserve customMapping) :> TypeReference
                elif x.IsRequiredModifier then
                    let x = x :?> RequiredModifierType
                    new Mono.Cecil.RequiredModifierType(x.ModifierType.ResolvePreserve customMapping, x.ElementType.ResolvePreserve customMapping) :> TypeReference
                elif x.IsOptionalModifier then
                    let x = x :?> OptionalModifierType
                    new Mono.Cecil.OptionalModifierType(x.ModifierType.ResolvePreserve customMapping, x.ElementType.ResolvePreserve customMapping) :> TypeReference
                elif x.HasGenericParameters then
                    let p = x.GenericParameters |> Seq.map (fun p -> p.ResolvePreserve(customMapping)) |> Seq.toList
                    if Seq.toList (x.GenericParameters |> Seq.map (fun x -> x :> TypeReference)) <> p then
                        let g = new Mono.Cecil.GenericInstanceType(x.TryResolve())
                        for i in p do
                            g.GenericArguments.Add i
                        g :> _
                    else
                        x.TryResolve()
                else
                    softAssert (List.contains (x.GetType ()) [typeof<TypeReference>; typeof<TypeDefinition>; typeof<GenericParameter>]) (sprintf "Can't work with Cecil types of type %O" (x.GetType()))
                    x.TryResolve ()

type MethodReference with
    member x.ResolvePreserve () = x.ResolvePreserve(fun _ -> None)
    member x.ResolvePreserve (customMapping) : MethodReference =
        if x.IsGenericInstance then
            let x = x :?> GenericInstanceMethod
            let newMethod = new Mono.Cecil.GenericInstanceMethod(x.GetElementMethod().ResolvePreserve(customMapping))
            for arg in x.GenericArguments do
                    newMethod.GenericArguments.Add (arg.ResolvePreserve(customMapping))
            newMethod :> MethodReference
        else
            let declaringType = x.DeclaringType.ResolvePreserve(customMapping)
            x.RebaseOn declaringType

    member x.RebaseOn(t: TypeReference): MethodReference =
        if t = x.DeclaringType then
            x
        else
        let newMethod = Mono.Cecil.MethodReference(x.Name, x.ReturnType, t)
        newMethod.MetadataToken <- x.MetadataToken
        x.Parameters |> Seq.iter newMethod.Parameters.Add
        x.GenericParameters |> Seq.iter newMethod.GenericParameters.Add
        newMethod.HasThis <- x.HasThis
        newMethod.ExplicitThis <- x.ExplicitThis
        newMethod

type FieldReference with
    member x.ResolvePreserve () = x.ResolvePreserve(fun _ -> None)
    member x.ResolvePreserve (customMapping) : FieldReference =
        let declaringType = x.DeclaringType.ResolvePreserve(customMapping)
        x.RebaseOn(declaringType)

    member x.RebaseOn(t: TypeReference): FieldReference =
        if t = x.DeclaringType then
            x
        else
        let newField = Mono.Cecil.FieldReference(x.Name, x.FieldType, t)
        newField.MetadataToken <- x.MetadataToken
        newField
