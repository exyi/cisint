module Interpreter
open System.Collections.Concurrent
open System.Threading.Tasks
open Expression
open InterpreterState
open Mono.Cecil
open FSharp.Control.Tasks.V2

type ExecutionCacheEntry = {
    ArgParameters: SParameter array
    /// condition -> state; the condition may contain some references to the resulting execution state (i.e. be dependent on some side effect result), but the system should try to reduce these
    DefiniteStates: (SExpr * ExecutionState) array
}

/// Cache of functions executed in full generality (from empty execution state and general parameters)
let private intCache : ConcurrentDictionary<MethodDefinition, Task<ExecutionCacheEntry>> = ConcurrentDictionary()
let private intAntiCycler : ConcurrentDictionary<MethodDefinition, bool> = ConcurrentDictionary()

let private getPreinterpretedMethod (method: MethodDefinition) =
    if intAntiCycler.TryAdd(method, true) then
        intCache.GetOrAdd(method, fun method -> task {
            return ({ ExecutionCacheEntry.ArgParameters = array<_>.Empty; DefiniteStates = array<_>.Empty })
        })
    else
        Task.FromResult({ ExecutionCacheEntry.ArgParameters = array<_>.Empty; DefiniteStates = array<_>.Empty })

let interpretMethod (method: MethodDefinition) (args: SExpr[]) (baseState: ExecutionState) = task {
    let! preinterpreted = getPreinterpretedMethod method
    ()
}