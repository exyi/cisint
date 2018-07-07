namespace Cisint.Core

module Intro =
    open Mono.Cecil.Cil

    let methodContainsXOR (assemblyPath: string) (typeName: string) (methodName: string) =
        let m = Mono.Cecil.ModuleDefinition.ReadModule(assemblyPath)
        let typeDef = m.GetTypes() |> Seq.find (fun t -> t.FullName = typeName)
//        let typeDef = typeRef.Resolve()
        let method = typeDef.Methods |> Seq.find (fun m -> m.Name = methodName)
        method.Body.Instructions |> Seq.exists (fun i -> i.OpCode.Code = Code.Xor)

