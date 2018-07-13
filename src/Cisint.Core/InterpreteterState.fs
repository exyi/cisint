module InterpreterState
open System.Collections.Immutable
open Expression
open TypesystemDefinitions
open Expression

type HeapObject = {
    Type: TypeRef
    TypeIsDefinite: bool
    Fields: dict<FieldRef, SExpr>
    IsShared: SExpr
}

[<CustomEquality>]
[<NoComparisonAttribute>]
type AssumptionSet = {
    Version: AssumptionSetVersion
    /// Set of expressions that are known to return true
    Set: ImmutableHashSet<SExpr>

    /// Set of all objects on the heap
    Heap: dict<SParameter, HeapObject>
} with
    interface System.IEquatable<AssumptionSet> with
        member a.Equals(b) = a.Set.SetEquals(b.Set)
    override a.Equals b =
        match b with
        | :? AssumptionSet as y -> a.Set.SetEquals(y.Set)
        | _ -> false
    override a.GetHashCode() =
        printfn "warn AssumptionSet.GetHashCode";
        failwith ""
        a.Set.Count // TODO

module AssumptionSet =
    let mutable private assumptionSetVersionCounter = 1L
    let private nextASVersion () =
        System.Threading.Interlocked.Increment(&assumptionSetVersionCounter) |> AssumptionSetVersion
    let empty = { Version = AssumptionSetVersion 0L; Set = ImmutableHashSet.Create<SExpr>(); Heap = dict<_, _>.Empty }
    // TODO: cache these guys, so ids remain the same for same version
    let add (assumptions: #seq<SExpr>) x =
        { x with Set = x.Set.Union(assumptions); Version = nextASVersion () }
    let addObj (objs: #seq<SParameter * HeapObject>) x =
        { x with Heap = x.Heap.AddRange(objs |> Seq.map (fun (a, b) -> System.Collections.Generic.KeyValuePair(a, b))) }

    let modObj key fn x =
        { x with Heap = x.Heap.SetItem(key, fn x.Heap.[key]); Version = nextASVersion () }


type ConditionalEffect = (SExpr * SideEffect)

and SideEffect =
    | MethodCall of MethodRef * resultValue: SParameter * args: SExpr array * virt: bool * globalEffect: bool * atState: AssumptionSet
    | FieldWrite of target: SParameter option * FieldRef * value: SParameter * atState: AssumptionSet
    | FieldRead of target: SParameter option * FieldRef * resultValue: SParameter * atState: AssumptionSet
    | Throw of value: SParameter * atState: AssumptionSet
    | Effects of ConditionalEffect array

type ExecutionState = {
    Parent: ExecutionState option
    SideEffects: ConditionalEffect list
    Conditions: SExpr array
    Assumptions: AssumptionSet
    // AssumptionsVersion: AssumptionSetVersion
    ChangedHeapObjects: SParameter clist
    Locals: dict<SParameter, SExpr>
    Stack: SExpr clist
} with
    member x.WithCondition (conditions: #seq<SExpr>) =
        { ExecutionState.Parent = Some x; SideEffects = list<_>.Empty; Conditions = IArray.ofSeq conditions; Assumptions = AssumptionSet.add conditions x.Assumptions; Stack = x.Stack; ChangedHeapObjects = []; Locals = x.Locals }
    member x.AddObject (objs: #seq<SParameter * HeapObject>) =
        { x with Assumptions = AssumptionSet.addObj objs x.Assumptions; ChangedHeapObjects = List.append (List.ofSeq <| Seq.map fst objs) x.ChangedHeapObjects }
    static member Empty = { ExecutionState.Parent = None; SideEffects = list<_>.Empty; Conditions = array<_>.Empty; Assumptions = AssumptionSet.empty; Stack = []; ChangedHeapObjects = []; Locals = dict<_, _>.Empty }

type InterpreterTodoTarget =
    | CurrentMethod of Mono.Cecil.Cil.Instruction * isLeave: bool
    | CallMethod of MethodRef * returnInstruction: option<Mono.Cecil.Cil.Instruction> * isVirtual: bool

type InterpreterTodoItem = {
    State: ExecutionState
    Target: InterpreterTodoTarget
}

type InterpretationResult =
    | NewState of ExecutionState
    | Branching of InterpreterTodoItem clist
    | Return of ExecutionState
