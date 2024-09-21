# Linear Core
### Core semantics for a lazy functional programming language with dependent types and linear resources.



## Terms
### [`Term.v`](/theories/Term.v)

Terms in this language (or, equivalently, its abstract syntax tree) are one of the following:
- The type of types. (**Type-in-type.** Not recommended for theorem provers.)
- The type of **propositions**.
- A **constructor**, with a unique identifier telling which constructor it is.
- A variable that should be **moved** into this position (and only this position).
- A **reference** that may not be moved here, but may be inspected non-destructively.
- **Application** of one term to another (ideally, a function or constructor applied to an argument or "struct member", respectively).
- The type of a function, or (equivalently) universal quantification over a proposition (i.e. "**for all**").
- Case analysis (i.e. "**match**").

Most of this is standard, but two notable characteristics differ from standard programming languages:
- **Match statements do not come packaged with their scrutinee.**
  In most languages, you'll see `match x with ...` or `match x { ...` or `case x of ...`.
  The interally AST doesn't follow that representation:
instead, match statements are represented as an application of a standalone match statement to a scrutinee.
  That is, with a syntax as close to the AST as possible, these statements might look like `(match ...) x`.
  In fact, match statments are the _only_ kind of function available, and they generalize the usual lambda-calculus function:
  any function taking an argument by name can be represented as a match statement with a single branch,
  whose pattern merely assigns its scrutinee a name without inspecting its structure whatsoever.
- There is one extra AST node called `Err` with no arguments. This represents an undesirable state, without elaboration.
  Why does this exist? This AST represents match statements as nested case analyses,
  in which each case holds one pattern, one body, and then all the next cases in the match, similar to a linked list.
  So what goes at the end of this list? `Err` does. Furthermore, types are designed to prevent `Err` from being reached,
  and so by structuring match statements this way, types naturally prove that matchings are exhaustive.



## Pattern-Matching
### [`Match.v`](/theories/Match.v)

Patterns are tricky to get right, but once they're right, in hindsight everything makes sense.

The most basic kind of pattern is a **strict pattern**, which is just a specific constructor applied to some named arguments.
Internally, this is a nested structure: a strict pattern is either _just_ a constructor or _another_ strict pattern with an extra named argument.

Above strict patterns, we have **reference patterns** and **move patterns**.
The intution here is that _move_ patterns are about _using_ resources while _reference_ patterns are about _looking_ at resources.
Move patterns work like any other language's patterns:
they wrap a strict pattern, and a successful match will destruct the original value and return its members/struct fields as movable resources.
Reference patterns, on the other hand, also wrap strict patterns, but successful matches can only produce more references.
Crucially, we can try to match a reference against multiple patterns and act differently in each branch, all without using the original resource.

Lastly, the full definition of a pattern is either a moved/strict pattern or a simple name binding.
The latter does not inspect its scrutinee at all, and, thanks to lazy execution, will not reduce it.
Simple name bindings allow the semantics to define lambda-calculus-style functions as single-case match statements.

The most complex and illustrative form of pattern matching is against a _reference to an application_.
Specifically, if we have a constructor (let's say a pair) taking two arguments (its left and right elements),
then each time we match a reference to that pair, we want
1. to reduce the term (which might be some complex computation returning a pair) just enough until it is literally a pair, then
2. to assign a name to each element of the pair as necessary, without evaluating them any further, then
3. to bind each name in the pattern to a _reference to_ those names we just created in the context.

So, for example, the term `let xy := (x, y) in match &xy with { &(a, b) => (a, b) }` should evaluate to `(&x, &y)` (and notably _not_ `(x, y)` or `&(x, y)`).
To do this, if `x` and `y` were not already named (e.g. if `xy` were `(0, 1)`), then we would edit the context such that,
for some names `l` and `r`, `xy` maps to `(l, r)`, `l` maps to `0`, and `r` maps to `1`.
In compiled implementations of these semantics, assigning names to subtrees should be a no-op, since each subtree already has a pointer address.
Name-binding is essentially a well-behaved substitute for arbitrary pointer addressing.



## Context & Substitution
### `TODO`

Variables are **linear**: that is, each variable must be moved (fully consumed, not just viewed) once and only once.
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
   The problem here is _where_ to substitute: specifically, where to _move_ the variable, and consequently which references come before the move.
   To figure this out _ahead_ of time would require evaluating the term before evaluating that same term.

A simple tweak, however, makes the first option work:
Rename everything until, at each AST node, any variable bound in one child subtree is not used in any other child subtree.
While awkward, this structure accurately represents a heap in which each distinct resource has a distinct address,
and each variable's scope is readable directly off the AST.
