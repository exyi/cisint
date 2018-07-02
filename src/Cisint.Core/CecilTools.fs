module CecilTools
open System.Collections.Concurrent
open System.Collections.Generic
open Mono.Cecil
open System
open System.Reflection

type private ModuleData = {
    Module: ModuleDefinition
    Types: Dictionary<string, TypeDefinition>
}

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

let convertType (t: Type) =
    let md = convertAssembly t.Assembly
    md.LookupToken(t.MetadataToken) :?> TypeDefinition
    // TODO: generic types

let convertMethodInfo (method: MethodInfo) : MethodDefinition =
    let md = convertAssembly method.DeclaringType.Assembly
    md.LookupToken(method.MetadataToken) :?> MethodDefinition

let convertFieldInfo (field: FieldInfo) : FieldDefinition =
    let md = convertAssembly field.DeclaringType.Assembly
    md.LookupToken(field.MetadataToken) :?> FieldDefinition