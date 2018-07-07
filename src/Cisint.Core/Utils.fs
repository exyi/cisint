[<AutoOpen>]
module Utils
open System.Collections.Immutable
open System
open System.Collections.Generic

type clist<'a> = list<'a>
type array<'a> = ImmutableArray<'a>
type list<'a> = ImmutableList<'a>
type dict<'a, 'b> = ImmutableDictionary<'a, 'b>

[<Struct>]
[<CustomEquality>] [<NoComparison>]
/// ImmutableArray with correct value-comparison
type EqArray<'a> = {
  arr: array<'a>
}
with
    member a.Equals b = Object.ReferenceEquals(a.arr, b.arr) || (a.arr.Length = b.arr.Length && Linq.Enumerable.SequenceEqual(a.arr, b.arr))
    interface IEquatable<EqArray<'a>> with
      member a.Equals b = a.Equals b
    override a.Equals b =
      match b with
      | :? EqArray<'a> as b -> a.Equals b
      | _ -> false
    override a.GetHashCode() =
      // PERF: specialize fold
      a.arr.Length * 319 + Seq.fold (fun s x -> (s * 19) + EqualityComparer.Default.GetHashCode x) 87654567 a.arr

module EqArray =
    let New arr = { EqArray.arr = arr }
    let OfSeq (s: #seq<_>) = New (ImmutableArray.CreateRange s)
    let inline (|AP|) arr =
      List.ofSeq arr.arr

module IArray =
  // PERF: maybe these should inline
  let map f (arr: 'a array) =
    let b = ImmutableArray.CreateBuilder(arr.Length)
    for i in arr do
      b.Add(f i)
    b.MoveToImmutable()
  let mapi f (arr: 'a array) =
    let b = ImmutableArray.CreateBuilder(arr.Length)
    for i = 0 to arr.Length - 1 do
      b.Add(f i arr.[i])
    b.MoveToImmutable()
  let collect (f: 'a -> #seq<'b>) (arr: 'a array) =
    let b = ImmutableArray.CreateBuilder()
    for i in arr do
      b.AddRange(f i :> seq<'b>)
    b.ToImmutable()
  let choose (f : 'a -> option<'b>) (arr: 'a array) =
    let b = ImmutableArray.CreateBuilder()
    for i in arr do
      match f i with
      | Some x -> b.Add(x)
      | None -> ()
    b.ToImmutable()
  let inline init count gen =
    let b = ImmutableArray.CreateBuilder(count)
    for i = 0 to (count - 1) do
      b.Add(gen i)
    b.MoveToImmutable()
  let ofSeq (a: #seq<'a>) = ImmutableArray.CreateRange a

// module SeqPlus =
//   let inline exactlyOneDistinct (arr: 'a seq) =
//     if arr.Length = 0 then None
//     else
//       let f = arr |>
//       for i in arr do
//         if

type internal Marker = interface end

let castAs<'T when 'T : null> (o:obj) =
  match o with
  | :? 'T as res -> res
  | _ -> null

let justAnd a b = a && b
let justOr a b = a || b

let waitForDebug () =
  if not(System.Diagnostics.Debugger.IsAttached) then
    printfn "Please attach a debugger, PID=%d" (System.Diagnostics.Process.GetCurrentProcess().Id)
    while not(System.Diagnostics.Debugger.IsAttached) do
        System.Threading.Thread.Sleep(100)
    System.Diagnostics.Debugger.Break()