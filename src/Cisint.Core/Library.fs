namespace Cisint.Core

module Say =
    let hello name =
        printfn "Hello %s" name


module Intro =
    open Mono.Cecil.Cil
    open Mono.Cecil.Cil

    let methodContainsXOR (assemblyPath: string) (typeName: string) (methodName: string) =
        let tt = struct (1, 2)
        printfn "%A %A" tt 1 // (tt.CompareTo(struct (4, 1)))
        let m = Mono.Cecil.ModuleDefinition.ReadModule(assemblyPath)
        let typeDef = m.GetTypes() |> Seq.find (fun t -> t.FullName = typeName)
//        let typeDef = typeRef.Resolve()
        let method = typeDef.Methods |> Seq.find (fun m -> m.Name = methodName)
        method.Body.Instructions |> Seq.exists (fun i -> i.OpCode.Code = Code.Xor)

