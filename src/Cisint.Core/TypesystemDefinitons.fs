module TypesystemDefinitions
open System
open Mono.Cecil

type TypeRef (cecilReference: TypeReference) =
    let hashCode = cecilReference.ToString().GetHashCode()
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
        a.Position = b.Position

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


    member _x.Definition = cecilDefintion.Value
    member _x.Reference = cecilReference
    member _x.Name = cecilReference.Name
    member _x.FullName = cecilReference.FullName
    member _x.IsPrimitive = cecilReference.IsPrimitive

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

type MethodRef(cecilReference: MethodReference) =
    let hashCode = cecilReference.ToString().GetHashCode()
    let cecilDefintion = lazy (cecilReference.Resolve())

    member _x.Definition = cecilDefintion.Value
    member _x.Reference = cecilReference
    member _x.ReturnType = TypeRef(cecilReference.ReturnType)

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

type FieldRef(cecilReference: FieldReference) =
    let hashCode = cecilReference.ToString().GetHashCode()
    let cecilDefintion = lazy (cecilReference.Resolve())

    member _x.Definition = cecilDefintion.Value
    member _x.Reference = cecilReference
    member _x.Name = cecilReference.Name
    member _x.FieldType = TypeRef(cecilReference.FieldType)

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