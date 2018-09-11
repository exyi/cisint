module TypesystemDefinitions
open System
open Mono.Cecil

// returns assignment of generic parameters - type parameter * argument
let private getGenericAssignment_type (typeDef: TypeDefinition) (typeRef: TypeReference) =
    match typeRef with
    | :? GenericInstanceType as d -> Seq.zip typeDef.GenericParameters d.GenericArguments
    | _ -> seq []
let private getGenericAssignment_method (methodDef: MethodDefinition) (methodRef: MethodReference) =
    let m =
        match methodRef with
        | :? GenericInstanceMethod as methodRef -> Seq.zip methodDef.GenericParameters methodRef.GenericArguments
        | _ -> seq []
    Seq.append m (getGenericAssignment_type methodDef.DeclaringType methodRef.DeclaringType)
let private createGenericParameterAssigner (values: seq<GenericParameter * TypeReference>) =
    let m = Linq.Enumerable.ToDictionary(values, (fun (a, _) -> (a.Position, a.Type)), (fun (_, b) -> b))
    if m.Count = 0 then fun a -> None
    else fun (x: TypeReference) ->
             match x with
             | :? GenericParameter as x ->
                 match m.TryGetValue ((x.Position, x.Type)) with
                 | (true, a) -> Some a
                 | (false, _) -> None
             | _ -> None

type TypeRef (cecilReference: TypeReference) =
    let rec checkGenerics (t: TypeReference) =
        softAssert (not t.HasGenericParameters) <| sprintf "Type %O has generic parameters" cecilReference
        match t with
        | :? GenericInstanceType as t ->
            t.GenericArguments |> Seq.iter checkGenerics
        | :? ArrayType as t ->
            checkGenerics t.ElementType
        | :? ByReferenceType as t ->
            checkGenerics t.ElementType
        | :? GenericParameter as p ->
            softAssert false <| sprintf "Type %O has generic parameter %O" cecilReference p
        | _ -> ()
    do checkGenerics cecilReference
    let cecilReference =
        // strip the modifiers
        match cecilReference with
        | :? RequiredModifierType as c -> c.ElementType
        | :? OptionalModifierType as c -> c.ElementType
        | _ -> cecilReference
    let hashCode =
        if cecilReference :? GenericParameter then
            let k = cecilReference :?> GenericParameter
            (k.Type, k.Position, 633567).GetHashCode()
        else
            cecilReference.ToString().GetHashCode()

    let cecilDefintion = lazy (cecilReference.Resolve())


    // Copy-pasted-translated code from Mono.Cecil, because they don't expose it as a public API...
    // https://github.com/jbevain/cecil/issues/389
    static member AreSameSpecifications (a: TypeSpecification) (b: TypeSpecification) =
        if not (TypeRef.AreSameTypes a.ElementType b.ElementType) then
            false

        elif a.IsGenericInstance then
            TypeRef.AreSameGenerics (a :?> GenericInstanceType) (b :?> GenericInstanceType)

        elif a.IsRequiredModifier || a.IsOptionalModifier then
            TypeRef.AreSameModifiers (box a :?> IModifierType) (box b :?> IModifierType)

        elif a.IsArray then
            TypeRef.AreSameArrays (a :?> ArrayType) (b :?> ArrayType)

        else true

    static member AreSameArrays (a: ArrayType) (b: ArrayType) =
        if a.Rank <> b.Rank then
            false

        // TODO: dimensions

        else true;

    static member AreSameModifiers (a: IModifierType) (b: IModifierType) =
        TypeRef.AreSameTypes a.ModifierType b.ModifierType

    static member AreSameGenerics (a: GenericInstanceType) (b: GenericInstanceType) =
        if a.GenericArguments.Count <> b.GenericArguments.Count then
            false
        else
            Seq.map2 (TypeRef.AreSameTypes) a.GenericArguments b.GenericArguments |> Seq.forall id

    static member AreSameGenericParams (a: GenericParameter) (b: GenericParameter) =
        a.Position = b.Position && a.Type = b.Type

    static member AreSameTypes (a: TypeReference) (b: TypeReference) =
        if Object.ReferenceEquals (a, b) then
            true

        elif (isNull a || isNull b) then
            false

        elif (a.MetadataType <> b.MetadataType) then
            false

        elif a.IsGenericParameter then
            TypeRef.AreSameGenericParams (a :?> GenericParameter) (b :?> GenericParameter)

        elif a :? TypeSpecification then
            TypeRef.AreSameSpecifications (a :?> TypeSpecification) (b :?> TypeSpecification)

        elif a.Name <> b.Name || a.Namespace <> b.Namespace then
            false

        //TODO: check scope

        else TypeRef.AreSameTypes a.DeclaringType b.DeclaringType

    static member CreateArray (element: TypeRef) =
        TypeRef (ArrayType element.Reference)
    static member CreateByref (element: TypeRef) =
        TypeRef (ByReferenceType element.Reference)

    member _x.Definition =
        softAssert (cecilDefintion.Value <> null) <| sprintf "Can't resolve type %O" cecilReference
        cecilDefintion.Value
    member _x.HasDefinition = cecilDefintion.Value |> isNull |> not
    member _x.Reference = cecilReference
    member _x.Name = cecilReference.Name
    member _x.FullName = cecilReference.FullName
    member _x.IsPrimitive = cecilReference.IsPrimitive
    member _x.IsObjectReference = not cecilReference.IsValueType && not cecilReference.IsPointer && not cecilReference.IsByReference
    member x.BaseType =
        if not x.HasDefinition || isNull x.Definition.BaseType then
            None
        elif cecilReference.IsGenericInstance then
            TypeRef (x.Definition.BaseType.ResolvePreserve x.GenericParameterAssigner) |> Some
        else
            TypeRef x.Definition.BaseType |> Some
    member x.BaseTypeChain =
        match x.BaseType with
        | Some bt ->
            x :: bt.BaseTypeChain
        | None -> [x]
    member x.Interfaces =
        let i = cecilDefintion.Value.Interfaces |> IArray.ofSeq |> IArray.map (fun t -> TypeRef (t.InterfaceType.ResolvePreserve x.GenericParameterAssigner))
        match x.BaseType with
        | None -> i
        | Some baseType -> IArray.append i baseType.Interfaces
    member x.GenericParameterAssigner = createGenericParameterAssigner (getGenericAssignment_type x.Definition cecilReference)
    /// Gets all fields with instantiated generic arguments, including base types
    member x.Fields =
        (match x.BaseType with
         | Some a -> IArray.append x.LocalFields a.Fields
         | None -> x.LocalFields)
    member private x.LocalFields : FieldRef array =
        // if not cecilReference.IsGenericInstance then IArray.ofSeq x.Definition.Fields |> IArray.map (FieldRef)
        // else
        IArray.ofSeq x.Definition.Fields |> IArray.map (fun f -> f.RebaseOn cecilReference |> FieldRef)
    /// Gets all methods with instantiated generic arguments, including base types
    member x.Methods =
        (match x.BaseType with
         | Some a -> IArray.append x.LocalMethods a.Methods
         | None -> x.LocalMethods)
    member private x.LocalMethods : MethodRef array =
        // if not cecilReference.IsGenericInstance then IArray.ofSeq x.Definition.Fields |> IArray.map (FieldRef)
        // else
        IArray.ofSeq x.Definition.Methods |> IArray.map (fun f -> f.RebaseOn cecilReference |> MethodRef)

    override x.Equals(o) =
        match o with
        | :? TypeRef as o -> hashCode = o.GetHashCode() && TypeRef.AreSameTypes x.Reference o.Reference
        | _ -> false

    override _x.GetHashCode () = hashCode
    override _x.ToString() = cecilReference.ToString()

    interface IEquatable<TypeRef> with
        member x.Equals(o) = hashCode = o.GetHashCode() && TypeRef.AreSameTypes x.Reference o.Reference

    new(td: TypeDefinition) =
        TypeRef(td :> TypeReference)

and MethodRef(cecilReference: MethodReference) =
    let hashCode = cecilReference.ToString().GetHashCode()
    let cecilDefintion = lazy (cecilReference.Resolve())

    member _x.Definition =
        softAssert (cecilDefintion.Value <> null) <| sprintf "Can't resolve method %O" cecilReference
        cecilDefintion.Value
    member _x.Reference = cecilReference
    member _x.Name = cecilReference.Name
    member x.ReturnType = TypeRef(cecilReference.ReturnType.ResolvePreserve x.GenericParameterAssigner)
    member _x.DeclaringType = TypeRef(cecilReference.DeclaringType)
    member x.ParameterTypes =
                                                                                     // v For some reason the parameters are not assigned in a reference
        let p = cecilReference.Parameters |> Seq.map (fun p -> TypeRef (p.ParameterType.ResolvePreserve x.GenericParameterAssigner))
        if cecilReference.HasThis then
            Seq.append [ (if x.DeclaringType.Reference.IsValueType then TypeRef (Mono.Cecil.ByReferenceType(x.Reference.DeclaringType)) else x.DeclaringType) ] p |> IArray.ofSeq
        else
            p |> IArray.ofSeq
    member x.Overrides =
        x.Definition.Overrides |> IArray.ofSeq |> IArray.map (fun m -> m.ResolvePreserve x.GenericParameterAssigner |> MethodRef)
    member x.GenericParameterAssigner = createGenericParameterAssigner (getGenericAssignment_method x.Definition cecilReference)

    static member AreSameMethods (a: MethodReference) (b: MethodReference) =
        if Object.ReferenceEquals(a, b) then
            true
        else
        TypeRef.AreSameTypes a.DeclaringType b.DeclaringType &&
            a.Name = b.Name &&
            a.Parameters.Count = b.Parameters.Count &&
            Seq.map2 (fun (a: ParameterDefinition) (b: ParameterDefinition) -> TypeRef.AreSameTypes a.ParameterType b.ParameterType) a.Parameters b.Parameters |> Seq.forall id
    override x.Equals(o) =
        match o with
        | :? MethodRef as o -> hashCode = o.GetHashCode() && MethodRef.AreSameMethods x.Reference o.Reference
        | _ -> false

    override _x.GetHashCode () = hashCode
    override _x.ToString() = cecilReference.ToString()

    interface IEquatable<MethodRef> with
        member x.Equals(o) = hashCode = o.GetHashCode() && MethodRef.AreSameMethods x.Reference o.Reference

    new(td: MethodDefinition) =
        MethodRef(td :> MethodReference)

and FieldRef(cecilReference: FieldReference) =
    let hashCode = cecilReference.ToString().GetHashCode()
    let cecilDefintion = lazy (cecilReference.Resolve())

    member _x.Definition =
        softAssert (cecilDefintion.Value <> null) <| sprintf "Can't resolve field %O" cecilReference
        cecilDefintion.Value
    member _x.Reference = cecilReference
    member _x.Name = cecilReference.Name
    member _x.DeclaringType = cecilReference.DeclaringType |> TypeRef
    member x.FieldType = TypeRef(cecilReference.FieldType.ResolvePreserve x.DeclaringType.GenericParameterAssigner)

    static member AreSameFields (a: FieldReference) (b: FieldReference) =
        if Object.ReferenceEquals(a, b) then
            true
        else
        TypeRef.AreSameTypes a.DeclaringType b.DeclaringType &&
            a.Name = b.Name
    override x.Equals(o) =
        match o with
        | :? FieldRef as o -> hashCode = o.GetHashCode() && FieldRef.AreSameFields x.Reference o.Reference
        | _ -> false

    override _x.GetHashCode () = hashCode
    override _x.ToString() = cecilReference.ToString()

    interface IEquatable<FieldRef> with
        member x.Equals(o) = hashCode = o.GetHashCode() && FieldRef.AreSameFields x.Reference o.Reference

    new(td: FieldDefinition) =
        FieldRef(td :> FieldReference)