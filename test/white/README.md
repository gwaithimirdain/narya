This directory contains "white-box" tests that call library functions directly, often using the Testutils utilities to construct terms by hand.

### Old-style interaction

Many of these tests use the interaction facilities in `Testutil.Mcp`, which was written before it was possible to typecheck definitions of constants.  Thus, it adds variables to the context rather than defining constants, and stores terms and values in OCaml variables.  The basic interaction functions in this package are:

- `synth M` -- Synthesize a type from a term `M` and return the corresponding "value" of `M` as well as the synthesized type (also a value).
- `check M T` -- Check the term `M` against the type `T`, which must be a value.  Returns the value of `M`.
- `assume "x" T` -- Assume a variable `x` of type `T` (a value), and return that variable (as a value).
- `equal R S` -- Assert that two values are definitionally equal.  They must be synthesizing, since this does no type-directed checking.
- `equal_at R S T` -- Assert that two values `R` and `S` are definitionally equal at the value type `T` (which they are assumed to belong to).
- `unsyth M` -- Verify that the term `M` *doesn't* synthesize.
- `uncheck M T` -- Verify that the term `M` *doesn't* typecheck at value type `T`.
- `unequal R S` -- Assert that two synthesizing values are *not* definitionally equal.
- `unequal_at R S T` -- Assert that two values `R` and `S` are *not* definitionally equal at the value type `T`.

In particular, a common idiom is

```
let theorem_ty, _ = synth "..."
let theorem = check "..." theorem_ty
```
That is, we first write the type of a theorem, synthesize it (its type will be `Type`, which we discard), and then check a proof of that theorem against the resulting value.  Of course this can be shortcut with
```
let theorem = check "..." (fst (synth "..."))
```
Since there wasn't a built-in notion of "definition", when a term will be used again later, it was convenient to give a name to its raw syntax also, e.g.
```
let rdefn = "..."
let defn = check rdefn defn_ty
```
