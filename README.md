# Linear Core

**In a word:** Purely functional programs that compile and run like low-level code.

The language guarantees a few great properties for anything written in it:
- **Copmile-time evaluation:** Everything that _can_ be evaluated at compile time _will_.
  - Many languages offer a small subset that can run at compile time: for example, C++'s `constexpr` or Rust's `const`.
    However, their designs prevent any non-trival compile-time evaluation _a priori_:
    everyone agress that a compiler should always finish and always spit out the same program, but
    most essential features of any popular language might either run forever (e.g. recursive functions)
    or access memory that varies between compiler runs (e.g. general pointer dereferencing).
    Here, on the other hand, evaluation is always deterministic and always terminates,
    so programs can be aggressively simplified at compile-time. In other words,
    compiler optimization and compile-time evaluation are one in the same:
    every program is always aggressively simplified, using the full range of language features,
    until it can't simplify any further, at which point compilation truly begins.
- **Dependent types:** Types and values are one in the same.
  - Most languages include a fixed-size array type as a special case, like C's `int array[42]` or Rust's `[int; 42]`.
    Here, however, you can define your own types that depend on values, then _compute a type_ at compile time (see above).
    For example, many communication protocols send the size of a message as the first part of that same message.
    With dependent types, you can straightforwardly write down the type of such a message,
    and the compiler will automatically check the correctness of any messages constructed.
    For example, if Rust supported this design, it might look something like this:
    ```rust
    struct msg { size: usize, data: [u8; size] }
    ```
    Note that the _type_ of `data` depends on the _value_ of `size`.
    Since types and values are on in the same, we first try to compute `size` at compile time;
    if we succeed, we can elide the `size` field entirely and allocate `data` on the stack,
    and if we can't, we wait until we receive `size` and allocate `data` at runtime.
- **Strong normalization:** Every computation terminates. No infinite loops.
  - In almost every programming language (and all popular ones),
    an accidental bug--even in someone else's library--can stop your code by looping forever.
    Here, we check at compile time that no infinite loop can exist.
- **Lazy evaluation:** If a term isn't used, it won't be evaluated.
  - What happens if you ask for the first element of `(42, <wait for 100 years>)`?
    In every popular language except Haskell, the code will wait for 100 years
    just to obtain a result that it will immediately throw away.
    Here and in Haskell, however, the code will look ahead and
    recognize that the second term will never be used,
    throwing it away before even starting to evaluate it.
- **Linear resources:** Nothing will ever be copied behind the scenes.
  - Even in "low-level" systems languages like C and C++,
    if you aren't extremely careful returning from a function,
    the compiler will automatically duplicate the result,
    no matter if it's a simple integer or a 50-gigabyte array.
    Here and in Rust, however, all automatic copies are explicitly outlawed;
    instead, the programmer has full control over when copies are made.
- **Static memory management:** No garbage collector necessary. In fact, no _heap_ is even necessary, if you opt out.
  - Garbage collectors are great for rapid prototyping, but
    they need to stop evaluation for milliseconds at a time to check--at runtime--if values are still lying around.
    This creates unavoidable issues in time-sensitive code,
    and, as a theoretical annoyance, it shouldn't be necessary.
    Furthermore, languages like Rust provide a heap opt-out feature (e.g. Rust's `no_std`)
    that allows the same language to write everything from high-level frontend software to low-level embedded code.
- **Purely functional:** Every function will always return the same result when called with the same arguments.
  - The benefits for testing are obvious--if a test fails, all you need to reproduce it is its arguments--but
    an underrated benefit is that it's good for _your sanity_. If you call a function, you know _exactly_ what's going on,
    and you can see at a glance the full set of influences on the function's result--and that's it.
    No more tracking down undocumented influences on an inexplicable subroutine. Breathe a sigh of relief.



## Terms

### [`Term.v`](/theories/Term.v)

All terms are one of the following:
- A **constructor**, with a unique identifier telling which constructor it is.
- A variable that should be **moved** into this position (and only this position) or **referenced** (inspected, but not moved).
- **Application** of one term (if all goes well, a function or constructor) to another term.
- A dependent **function type**, written `forall` in general or `->` in non-dependent types.
- **Case** analysis: a pattern, a body if the pattern matches, and an alternate body if it doesn't match.

Most of this is standard, but the main difference from standard languages is that
_match statements do not come packaged with their scrutinee_.
In most languages, you'll see `match x with ...` or `match x { ...`.
The interal AST doesn't follow that representation:
instead, match statements are represented as an application of a standalone match statement to separate scrutinee.
That is, with a syntax as close to the AST as possible, these statements might look like `(match ...) x`.



## Pattern-Matching

### [`Match.v`](/theories/Match.v)

The most basic kind of pattern is a **strict pattern**: a specific constructor applied to some named arguments.
Internally, this is a nested structure: either *just* a constructor or *another* strict pattern applied to an extra named argument.

Wrapping strict patterns are **reference patterns** and **move patterns**.
The intution here is that *move* patterns are about *using* resources while *reference* patterns are about *looking* at resources.
Move patterns work like any other language's patterns:
they wrap a strict pattern, and a successful match will destruct the original value and return its members/struct fields as movable resources.
Reference patterns, on the other hand, also wrap strict patterns, but successful matches can only produce more references.
Crucially, we can test a reference against a pattern and step to different terms in matching or non-matching cases, all without using the original resource.

The full definition of a pattern is either a moved/strict pattern or a simple name binding.
The latter does not inspect its scrutinee at all, and, thanks to lazy execution, will not reduce it.
Simple name bindings allow the semantics to define lambda-calculus-style functions as single-case match statements.

The most complex and illustrative form of pattern matching is against a *reference to an application*.
Specifically, if we have a constructor (let's say a pair) taking two arguments (its left and right elements),
then each time we match a reference to that pair, we want
1. to reduce the term (which might be a complex computation reducing to a pair) just enough until it is literally a pair, then
2. to assign a name to each element of the pair, without evaluating them any further, then
3. to bind each name in the pattern to a *reference* to those names we just created in the context.

So, for example, if `&x` denotes a reference to the variable `x`, then
the term `let xy := (x, y) in match &xy with { &(a, b) => (a, b) }` should evaluate to `(&x, &y)` (and notably *not* `(x, y)` or `&(x, y)`).
To do this, if `x` and `y` were not already named (e.g. if `xy` were `(0, 1)`), then we would edit the context such that,
for some names `l` and `r`, `xy` maps to `(l, r)`, `l` maps to `0`, and `r` maps to `1`.
In compiled implementations of these semantics, assigning names to subtrees should be a no-op, since each subtree already has a pointer address.
Name-binding is essentially a well-behaved substitute for arbitrary pointer addressing.



## Context & Substitution

### [`Context.v`](/theories/Context.v)

Variables are **linear**: that is, each variable must be moved once and only once.
During execution, until a variable is moved, references can view its structure arbitrarily many times.

Here's exactly what variables should do:
- Until a variable has been moved, it can be referenced arbitrarily many times.
  - References can be reduced to decide a match statement.
    - This should happen globally: i.e., to the referenced value, not to each reference location individually.
- Once a variable is moved, it is removed from the context and dropped in as if handwritten in place.
- After a variable has been moved, execution continues as if it had never been bound.
- If, after control flow exits a variable's scope, it has not been moved, execution fails.
  - Equivalently, every variable must be used.

Representing this behavior is difficult. There are roughly three options:

1. A **finite map**, e.g. a binary search tree, from names to terms. This is standard for classical (non-linear) semantics, but it presents a few issues.
   Most of all, **scope** is tricky. Names can jump ship if not contained:
   for example, `match (let x = 42 in 0) with { 0 => x }` needs to reduce the scrutinee `let x = 42 in 0` because the pattern `0` is a constructor,
   which will put `x = 42` in the context; then, `match 0 with { 0 => x }` will simplify to `x`; then, `x` will look up `x` and evaluate to `42`.

2. A **tree**. This is relatively standard for some substructural type systems. And this solves the scope problem:
   if we know that `x` is bound only in the scrutinee branch of the AST, then we can check that the scope branch of the context is empty before matching.
   However, this creates a problem with laziness in variables: in eager languages, variables have been fully reduced and thus don't need context,
   but since variables can be bound without being evaluated, they may contain raw variable names that need context.
   The type of such a map would have to contain itself as a dependent argument.

3. **No context**. In other words, immediately substitute every variable when it's defined, and don't carry anything around.
   The problem here is *where* to substitute: specifically, where to *move* the variable, and consequently which references come before the move.
   To figure this out *ahead* of time would require evaluating the term before evaluating that same term.

A simple tweak, however, makes the first option work:
Rename everything until, at each AST node, any variable bound in one child subtree is not used in any other child subtree.
While awkward, this structure accurately represents a heap in which each distinct resource has a distinct address,
and each variable's scope is readable directly off the AST.
