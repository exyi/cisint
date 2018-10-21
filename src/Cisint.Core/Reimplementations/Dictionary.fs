module Reimplementations.Dictionary
open System.Collections.Generic
open System
open InterpreterState
open TypesystemDefinitions

let private keyNotFound =
    function
    | Some x -> x
    | None -> raise (KeyNotFoundException "The given key was not present in the dictionary.")

type private DictionaryReimpl<'k, 'v> when 'k : equality () = class

    let mutable values : ('k * 'v) [] = Array.zeroCreate 10
    let mutable count = 0

    let findIndex (key: 'k) =
        let mutable result = None
        for i in 0..(values.Length-1) do
            let kvp = values.[i]
            if not (isNull (box kvp)) then
                let (k, v) = kvp
                if k.Equals(key) then result <- Some i
        result

    member x.Find (key: 'k) =
        let mutable result = None
        for i in 0..(values.Length-1) do
            let kvp = values.[i]
            if not (isNull (box kvp)) then
                let (k, v) = kvp
                if k.Equals(key) then result <- Some kvp
        result

    member x.Insert rewrite key value =
        match (rewrite, findIndex key) with
        | (_, None) ->
            values.[count] <- (key, value)
            count <- count + 1
        | (true, Some oldIndex) ->
            values.[oldIndex] <- (key, value)
        | (false, Some _oldIndex) ->
            raise (ArgumentException("An item with the same key has already been added."))
    member x.Item
        with get(key) = x.Find key |> keyNotFound |> snd
        and set (key) value = x.Insert true key value
    member x.Keys = values |> Array.choose (fun v -> if isNull (box v) then None else Some (fst v)) :> ICollection<'k>
    member x.Values = values |> Array.choose (fun v -> if isNull (box v) then None else Some (snd v)) :> ICollection<'v>
    member x.Count = count
    member x.IsReadOnly = false
    member x.Add (k, v) = x.Insert false k v
    member x.Add (KeyValue(k, v)) = x.Insert false k v
    member x.Clear () =
        count <- 0
        values <- Array.zeroCreate 100
    member x.Contains (KeyValue(k, v)) =
        match x.Find k with
        | None -> false
        | Some (_k, v2) -> Object.Equals(v2, v)

    member x.ContainsKey k = x.Find k |> Option.isSome
    member x.CopyTo (array : KeyValuePair<'k, 'v> [], aIndex: int) =
        let mutable aIndex = aIndex
        for i in 1..values.Length do
            let kvp = values.[i]
            if not (isNull (box kvp)) then
                let (k, v) = kvp
                array.[aIndex] <- KeyValuePair(k, v)
                aIndex <- aIndex + 1
    member x.TryGetValue(key, value: 'v byref) =
        match x.Find key with
        | None -> false
        | Some (_, x) ->
            value <- x
            true

    member x.Remove key =
        match findIndex key with
        | None -> false
        | Some index ->
            count <- count - 1
            values.[index] <- Cisint.DynamicEvaluator.Evaluator.GetDefault<'k * 'v>()
            true
    member x.Remove (KeyValue(k, v: 'v)) =
        match findIndex k with
        | None -> false
        | Some index ->
            if Object.Equals(v, snd values.[index]) then
                count <- count - 1
                values.[index] <- Cisint.DynamicEvaluator.Evaluator.GetDefault<'k * 'v>()
                true
            else false

    member x.GetEnumerator() =
        (values |> Seq.choose (fun v -> if isNull (box v) then None else Some (KeyValuePair(fst v, snd v)))).GetEnumerator()
    interface IDictionary<'k, 'v> with
        member x.Item
            with get(key) = x.[key]
            and set (key) value = x.[key] <- value
        member x.Keys = x.Keys
        member x.Values = x.Values
        member x.Count = count
        member x.IsReadOnly = false
        member x.Add (k, v) = x.Add (k, v)
        member x.Add a = x.Add a
        member x.Clear () = x.Clear()
        member x.Contains a = x.Contains a
        member x.ContainsKey k = x.ContainsKey k
        member x.CopyTo (array, aIndex) = x.CopyTo(array, aIndex)
        member x.TryGetValue(key, value: 'v byref) = x.TryGetValue(key, &value)

        member x.Remove (key: 'k) = x.Remove key
        member x.Remove (a:KeyValuePair<'k, 'v>) = x.Remove a

        member x.GetEnumerator() = x.GetEnumerator()
        member x.GetEnumerator() =
            (values |> Array.choose (fun v -> if isNull (box v) then None else Some (KeyValuePair(fst v, snd v)))).GetEnumerator()

end

let private getType (t: TypeRef) =
    let rawType = CecilTools.convertTypeToRaw typedefof<DictionaryReimpl<int, int>>
    let generic = Mono.Cecil.GenericInstanceType rawType
    for i in t.Definition.GenericParameters do
        generic.GenericArguments.Add i
    let generic = generic.ResolvePreserve t.GenericParameterAssigner
    printfn "Converted %O -> %O" t generic
    TypeRef generic
let private findMatchingMethod (method: MethodRef) =
    let dt = getType method.DeclaringType
    let translateArgType (t: TypeRef) =
        TypeRef (t.Reference.ResolvePreserve (fun t -> if TypeRef.AreSameTypes t method.DeclaringType.Reference then
                                                           Some dt.Reference
                                                       else None))
    dt.Methods |> Seq.tryFind (fun m ->
        m.Name = method.Name && m.ParameterTypes.Length = method.ParameterTypes.Length && (m.ParameterTypes |> IArray.map translateArgType) = (method.ParameterTypes |> IArray.map translateArgType))


let reimplementDictionary (e: ExecutionServices) =
    { e with
        InterpretMethod = fun method state args services ->
            if method.DeclaringType.Definition.FullName = "System.Collections.Generic.Dictionary`2" then
                let m2 = findMatchingMethod method |> Option.defaultWith (fun x -> failwithf "Could not find reimplementation for %O" method)
                printfn "Replacing %O with %O" method m2

                let state =
                    if method.Name = ".ctor" then
                        // initialize the object before invoking constructor
                        let (newObjP, state) = StateProcessing.createEmptyHeapObject m2.DeclaringType state
                        let obj = state.Assumptions.Heap.[newObjP]
                        let state = obj.Fields |> Seq.fold (fun state (KeyValue(field, value)) ->
                                        StateProcessing.setField args.[0] field value state
                                    ) state
                        state
                    else
                        state

                e.InterpretMethod m2 state args services
            else
                e.InterpretMethod method state args services
    }