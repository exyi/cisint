module InterpreterState
open System.Collections.Immutable
open Expression
open Mono.Cecil

type ConditionalEffect = (SExpr * SideEffect)

and SideEffect =
    | MethodCall of MethodReference * resultValue: SParameter * args: SExpr array * virt: bool
    | FieldWrite of SParameter option * FieldReference
    | FieldRead of SParameter option * FieldReference * resultValue: SParameter
    | Effects of ConditionalEffect array

type HeapObject = {
    Type: TypeReference
    TypeIsDefinite: bool
    Fields: ImmutableDictionary<FieldReference, SExpr>
    IsShared: SExpr
}

type ExecutionState = {
    Parent: ExecutionState option
    SideEffects: ConditionalEffect list
    Assumptions: SExpr array
    AssumptionsVersion: AssumptionSetVersion
    HeapObjects: ImmutableDictionary<SParameter, HeapObject>
    Stack: SExpr clist
}
