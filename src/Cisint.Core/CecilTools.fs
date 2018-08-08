module CecilTools
open System.Collections.Concurrent
open System.Collections.Generic
open Mono.Cecil
open System
open System.Reflection
open TypesystemDefinitions

type private ModuleData = {
    Module: ModuleDefinition
    Types: Dictionary<string, TypeDefinition>
}

type GeneralSentinelType = { A: int }

let private assemblyCache = ConcurrentDictionary<string, ModuleData>()
let private loadModuleCached (location: string) =
    assemblyCache.GetOrAdd (location, fun l ->
        let md = ModuleDefinition.ReadModule l
        let types = Dictionary()
        md.GetTypes() |> Seq.iter (fun t -> types.Add (t.FullName, t))
        { ModuleData.Module = md; Types = types }
    )
let convertAssembly (assembly: Assembly) =
    (loadModuleCached assembly.Location).Module

let convertTypeToRaw (t: Type) =
    softAssert (not t.IsConstructedGenericType) "Can't convert generic types"
    let md = convertAssembly t.Assembly
    md.LookupToken(t.MetadataToken) :?> TypeDefinition
    // TODO: generic types

let convertType t = convertTypeToRaw t |> TypeRef

let convertMethodInfo (method: MethodInfo) : MethodRef =
    let md = convertAssembly method.DeclaringType.Assembly
    md.LookupToken(method.MetadataToken) :?> MethodDefinition |> MethodRef


let convertFieldInfo (field: FieldInfo) : FieldRef =
    let md = convertAssembly field.DeclaringType.Assembly
    md.LookupToken(field.MetadataToken) :?> FieldDefinition |> FieldRef

let boolType = convertType typeof<bool>
let objType = convertType typeof<obj>
let intType = convertType typeof<int>
let nintType = convertType typeof<IntPtr>
let nuintType = convertType typeof<UIntPtr>
let enumType = convertType typeof<System.Enum>
let generalSentinelType = convertType typeof<GeneralSentinelType>
