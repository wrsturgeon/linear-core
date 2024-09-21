# Linear Core

Core semantics for a lazy functional programming language with dependent types and linear resources.

At a glance, here's the abstract syntax tree in Backus-Naur form:

Terms and types:
```ebnf
<term> ::=
  | Error
  | Type
  | Proposition
  | Constructor <constructor>
  | Move <name>
  | Reference <name>
  | Application <term> <term>
  | Forall <name> <term> <term>
  | Case <pattern> <term> <term>
```

Patterns:
```ebnf
<pattern> ::=
  | Bind <name>
  | Inspect <move-or-reference>

<move-or-reference> ::=
  | MovePattern <strict-pattern>
  | ReferencePattern <strict-pattern>

<strict-pattern> ::=
  | ConstructorPattern <constructor>
  | ApplicationPattern <strict-pattern> <name>
```

Constructors:
```ebnf
<constructor> ::=
  | Builtin <builtin-constructor>
  | UserDefined <name>
```

Non-empty strings:
```ebnf
<name> ::= <character> <string>
```



## Terms ([`Term.v`](/theories/Term.v))

All terms are one of the following:
- A **constructor**, with a unique identifier telling which constructor it is.
- A variable that should be **moved** into this position (and only this position).
- A **reference** to be inspected but not yet moved.
- **Application** of one term to another.
- A dependent **function type**, written `forall` in general or `->` in non-dependent settings.
- **Case** analysis: a pattern, a term if the pattern matches, and another term if it doesn't.
- The type of **propositions**.
- The **type of types**. (Type-in-type: not recommended for theorem provers.)

Most of this is standard, but two notable characteristics differ from standard programming languages:
- Match statements do not come packaged with their scrutinee.
  In most languages, you'll see `match x with ...` or `match x { ...` or `case x of ...`.
  The interal AST doesn't follow that representation:
  instead, match statements are represented as an application of a standalone match statement to separate scrutinee.
  That is, with a syntax as close to the AST as possible, these statements might look like `(match ...) x`.
- The last kind of AST node, called `Err`, instructs the type system to check that a region cannot be reached.
  For example, many languages support exhaustive match statements. These statements can desugar to nested case analyses
  whose final alternate term is `Err`, and the type system will check that at least one pattern will match.



## Pattern-Matching ([`Match.v`](/theories/Match.v))

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



## Context & Substitution (`TODO`)

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
