# CISINT - .NET CIL symbolic interpreter

As you could guess from the name, this is a library for symbolic execution of .NET code. It is intended for execution of specific method, not the whole program and it tries to perform full analysis of the program - not just a few of selected paths that were found. When some methods can not be fully understood, they are considered a side effect of any code that invokes the function.

For example, suppose you have a function `let makeTuple (x:int) = (x, x + 1)` (returns a tuple of `x` and `x + 1`. When you try to execute it with generic parameter named `a` you will essentially get the function decompiled (just to a strange language) - it will say that function return a new object of type `System.Tuple``2<System.Int32,System.Int32>` that has field `m_Item1` set to `a` and `m_Item2` set to `a + 1`. This is how the output currenlty looks like:

```
.heapStuff {
        let o1 = new System.Tuple`2<System.Int32,System.Int32>
        o1.m_Item1 = a
        o1.m_Item2 = (a + 1)
}

return [
        o1
]
```

> Note that this language is just a "debug view" of the state, and it's syntax is pretty arbitrary.

The fun begins when you use this object in another function -- suppose we have functions `let sumTuple (a: int, b) = a + b` and `let fn a = sumTuple (makeTuple a)`. When we execute `fn` with a generic parameter we get only this:

```
return [
        (a + (a + 1))
]
```

Although the tuple object was allocated, when it was used the interpreter when what's inside, so it has just inlined the value. And because the object is not used anywhere it's not displayed at all.

> Note that F# compiler is capable of doing this optimizing this funciton itself, but it's only limited to tuples.

The main strength of this thing is executing functions when only some parameters are genric. For example, when you have a higher order function that is invoked with a lambda expression (essentially a "code constant") like this:

```fsharp
let seqMap (fn: 'a -> 'b) (xs: 'a seq) =
	seq { for i in xs do yield fn i }
let seqCreate count value =
	seq { for _ in 1..count do yield value }

let fn (a: int) (b: int) =
	seqCreate a b |> seqMap (fun a -> a * a) |> Seq.sum
```

When you try to execute `fn 3 b` you will get a result like `b*b + b*b + b*b` although executing just `seqMap` would fail. If you'd like to appreciate the capabilities of the interpreter, have a look at [the code generated from the `seq` computation expressions](https://sharplab.io/#v2:DYLgZgzgPg9gDgUwHYAIDKBPCAXBBbAWAChsNF0Y8FsALASyQHMUBeFAY2AEMIJiUBKHF2x12KKngBGCAE7oEARwCyXOCgAUYJCBQByLigC0APn1SAlJoAeEXQaFKrLfoLcQlKAN4owMeXQoDCi2KAAmMCgYdAjAYb6ogQC+rgLCouKSMvJoSgDCsggiCBwwAK5I2CgAblzAZSUuRG7unj5+AUGoAIwAdL3s5ZXhkdGx8bX1JSlEqULYImIS+NkoAGJoNFyycAAyXNJhPACCSGG5ippcugzYznNuaJTU9Ey9FwVFuCiGhlBmTyotAYjHeSlU6i0FR+xjMhgAVD8rP8FIpehAyoQiMgwkA===)

### Limitations

The interpreter is quite powerful, but there is also a lot of limitations. Specifically these are not supported:

* Obscure and unsafe IL instructions
* Delegates (and C# lambdas)
* Most exception handlers (unless it figures out that `try` or `finally` section does nothing)
* Cycles when the condition can not be computed
* Functions with too many jumps (by default 100). It's there to prevents stalls on complex computations and infinite cycles.
* Methods that don't have IL body.
* When compiled in RELEASE, functions that trigger an unexpected exceptions are also considered uninterpretable. In DEBUG, the exception will not be catched and it will crash the entire interpreter.

In most cases the interpreter will return the correct result or say that it can't interpret the function. Except for a few cases where it deviates from the .NET runtime specification:
* When the code depends on exception from a primitive operation (like a cast of an object), but does not use it's value.
	- When the value is used, the cast is reflected somewhere in the tree, so it should be equivalent with the original code.
	- This is probably a necessary compromise since it's pretty rare and checking each overflow, cast or null reference would overwhelm the output by a ton side-effects and make it practically unusable.
* Although there is a protection against infinite loops and stuff like that, in some cases the interpreter may end up with stack overflow exception, out of memory exception or may simply take too much time to run. It's not great, but at least does not produce bad results.

### Side effects

When something unsupported is encountered, the function is marked as *too complicated* and it's considered to be a side-effect of the computation. All side effects are tracked in the original order (with conditions under which can it happen). For example, functions that are using C#'s `yield return` do some optimization if the current thread has not changed by calling `Thread::GetCurrentThreadNative` and `Thread::GetCurrentThreadNative`. These invocations are tracked as side effects and it's return values introduce new symbolic parameters and some expressions may depend on them. In case of the iterators, the behavior is the same regardless of the function result, so the symbolic parameter is likely not used anywhere and the result might look like this:

```

se102 := global. System.Threading.Thread System.Threading.Thread::GetCurrentThreadNative()()
.heapStuff {
	let se102 = new System.Threading.Thread
	shared se102
}
se103 := global. System.Int32 System.Threading.Thread::get_ManagedThreadId()(se102)
se104 := global. System.Threading.Thread System.Threading.Thread::GetCurrentThreadNative()()
.heapStuff {
	let se104 = new System.Threading.Thread
	shared se104
}
se105 := global. System.Int32 System.Threading.Thread::get_ManagedThreadId()(se104)
if !(se103 = se105) {
	 * 	se106 := global. System.Threading.Thread System.Threading.Thread::GetCurrentThreadNative()()
	 * 	.heapStuff {
			let se106 = new System.Threading.Thread
			shared se106
		}
		se107 := global. System.Int32 System.Threading.Thread::get_ManagedThreadId()(se106)
}

return [
	-97
]

```

You may have noticed the **shared** statement in the code above. It basically means that everything in this object may be in any state and it can be shared with another thread and every read and write to it is considered a side-effect. Fortunatelly, in this case, the computation was not dependent on the result of these methods and always returns -97.

### Program state

When the code is interpreted, the interpreter keeeps it's state (locals, parameters, IL stack, objects) in the same `ExecutionState` record that is used to communicate out the result of the computation. Most of the state info is stored in the form of symbolic expressions -- when you have a value somewhere it can be either a constant, symbolic parameter or an expression like `a + 1` or `if (x = 1) { y } else { z }`. These expressions represent values on the IL stack, in local variables, in fields of objects on the heap or elements of an array, they can contain references to another objects, invocation of pure functions, invocations of instructions, conditions and constants. The state may be formatted to the pseudocode you have seen above -- the code has a few important features:

* It always starts with a list of side effects.
	- Field read/writes are represented intuitively as a assignment (`<-`) or parameter definition (`:=`).
	- Method calls are represented as a method full name (including full signature) and a arguments in brackets. There is usually a parameter defined for the result value.
		There may a `.global` prefix if the method call may have observable effect on the entire environment and there may be `.virt` prefix if the call is virtual.
		For example: `se92 := global. System.Int32 Cisint.Tests.TestInputs.Something::SideEffect2(System.String)(y)`
	- If the  is conditioned, it's wrapped in a `if` block.
* Then there are expressions on the IL stack - usually a result value of a method call
* `.heapState` blocks - when the side-effect or result depends on some objects, they are introduced and put into the correct state in this block. It may contain the following constructs:
	- `let p = new Obj` - declares new parameter and assigns an uninitialized object into it
	- `def p : Obj` - declares new parameter and says that it has type `Obj`. In this case, it can also contain object of a derived type.
	- `p.f = expr` - assigns `expr` to field `f`
	- `shared x [iff condition]` - if the condition holds, the object is in a **shared** state


### Expression simplifier

To figure out what is in the symbolic expressions, we have a simplifier -- it takes a expression and tries to reduce it's complexity. Specifically, it should figure out that a expression is always `true`/`false` to prevent reduntant branches, it should fold constant (i.e. `1 + 1` -> `2`), and transform equivalent expressions into a common shape (`a + b` <--> `b + a`). It's quite common for symbolic execution engines to use some SMT solver, this simplifier is a very basic compared to that, but it can IMHO handle lot of practical use cases. Unfortunatelly, it's not very powerful, so you can't expect it to understand hash-tables or quick-sort. Overall, it does something, but I'm not very satisfied with it's capabilities, I'll have to look how to write these things...

### Extensibility

When looking at the result of the interpretation is not enough for you (because it was not able to understand something, you don't want it to implement something, ...) there are some extensibility option. The main "entry point function" `Interpreter.interpretMethod` takes an argument of type `ExecutionServices` which contains few function that you may find good to override. Specifically, you can provide custom implementation (or decorated version of the default one) of recursive `InterpretMethod`, custom logic for accessing static field (they may often contain predictable data, even though in general case we can't assume much about them). You may also provide information about method that are considered a side-effect and a dispatcher of computation frames, if you have a smart way of planning them.


