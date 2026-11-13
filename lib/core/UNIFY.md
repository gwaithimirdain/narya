# Unification: design, decisions, and open points

This file records the design of unification metavariables, the solver, and
constraint postponement as implemented on the `unif-metas` branch
(November 2026), together with the reasons for the main decisions, the
experiments that were tried and rejected, and what remains open.  It builds
on `EQUAL.md`, which describes the conversion checker this extends; read
that first for the spine-first/local-unfolding structure of `equal.ml`.

Code map:

| Where | What |
| --- | --- |
| `term.ml`, `value.ml` | `meta_kind = Global_meta \| Unif_meta of term option ref`; `Blocked` evaluations and `Blocked_on` lazy states |
| `global.ml` | per-command `Uniftable` (`Unifdata`), `Postponed` constraints, retries, `finish_unifs`, reporting |
| `norm.ml` | evaluation of unsolved metas, `force_eval`'s caching rule |
| `equal.ml` | three-valued results (`Unequal` / `Stuck`), `with_solver`, flexible spine comparison, memo of flexible comparisons, the flexibly-stuck rule |
| `unify.ml` | the solver (`try_solve`, `try_expand`, `refine_to_constr`, `solve_singletons`), installed into `Equal.solver` |
| `readback.ml` | `renamed_ctx`, `invert_value`, the `Unifying` readback mode (occurs/scope checks, inversion, prekeys, candidates), `readback_unif_solution` |
| `check.ml` | `make_unif`, `check_synthesized` (guarded terms), `postpone_problem`, `retrying` / `validate`, placeholder boundaries, the expander |
| `test/black/unif.t` | the tests, almost all of them black-box (about 3900 lines), each solution checked definitionally where possible |

## 1. Guiding policy

**Only most general solutions.**  The solver solves a metavariable only
when the solution it finds is the unique most general one (MGU).  Anything
else is postponed and, if never decided, reported as an error.  There are
no heuristic or "lossy" solutions (first-order argument matching in
non-injective spines, as Rocq's evarconv does and Lean does with
backtracking), and no defaulting of leftovers at the end of a command.  The
reason is predictability: a user can tell in advance whether a placeholder
will be solved, and a solution never depends on the order in which
constraints happen to be encountered.  This policy came up over and over,
and it drove most of the decisions below.  It costs some performance (see
§8): Agda's `--lossy-unification` exists because MGU-only was too slow for
some users, and we accept that kind of cost.

**The key lemma.**  If a metavariable's environment and arguments send its
context's variables to *plain variables* (a renaming), substituting them
causes no computation: evaluation never compares levels.  So if a value
`v` contains only variables in the image, the read-back term is the unique
solution, *even if the renaming is not injective*, as long as `v` avoids
the variables that are images of more than one variable (or of one with the
wrong modal annotation).  Any solution using a preimage of such a variable
would put that variable in `v` as well.  (Kovács's work accepts the same
argument.)  The rest of the solver extends what counts as "a renaming"
while keeping this argument valid: permutations, keys, tuples and
abstractions of variables, cube faces, modal fields.  It always rejects
anything whose substitution could compute, such as constructors, proper
degeneracies of applied variables (`a ↦ refl Y`, where `a .trr y`
reduces), blocked entries, and rigid neutrals (which would need head
avoidance, i.e. pruning).

**Solutions are not re-checked.**  `Global.solve_unif` records a solution
without typechecking it.  The solver must therefore produce well-typed
solutions by construction.  An arity-0 bug (cube dimensions are not
determined by face lists when there are no endpoints) once produced an
ill-typed solution this way, which is why the inversion code compares
dimensions explicitly (§5.4).

## 2. Metavariables

### Representation

- `Term.Meta (meta, kind, energy)` / `Value.Meta {meta; kind; env; ins}`,
  where `meta_kind` is `Global_meta` (holes, let-bound and other internal
  definitions) or `Unif_meta of term option ref`.  The kind is indexed by
  the meta's energy *and* the occurrence energy, so unification metas and
  their occurrences are kinetic only; at a case-tree leaf a placeholder is
  `Realize (make_unif …)`.  The user rejected two alternatives: a `flex`
  sum type with parallel constructors holding the same data, and a custom
  mutable record.  The cell is a plain `ref`.
- **Per-command table.**  Unification metas live in `Global.Uniftable`,
  part of the `Speculable` `current_command` state: type, creation context,
  a lazily read-back termctx, the cell, the speculation depth, location +
  error code, and the `delayed` flag (§6).  A unification meta exists only
  during its command: by the end it is either solved or the command fails.
  So none of this is marshaled, and speculation rollback discards the metas
  created inside the speculation.
- **Solutions are written into the cell as soon as they're found**
  (`Global.set_unif_solution`), and the cell is the only record of a
  solution.  The depth rule (below) makes this safe: a speculation can
  solve only the metas created inside it, so a solution is backtracked only
  together with its meta, which is discarded along with everything that
  refers to it.  Its cell may be left written, but nothing can reach it.
  At the end of the command (`finish_unifs`), unsolved cells get `Failed`,
  even if the command failed, because its constants may still be used by
  later commands.  `link.ml` inlines written cells, and an unwritten cell
  there is an anomaly.
  - *History*: cells were at first written only at the end of the command,
    simply as the easiest choice to start with.  Solutions lived in the
    table until then, and `force_eval` had a third status, `Speculative`,
    which re-ran blocked recipes without caching them.  Writing at solve
    time (2026-11-13) removed that status, the table's solution field, and
    a table lookup on every force of a blocked value.  It cost nothing on
    ordinary code (hott.t −0.004%, sym orig 63 +0.02% instructions) and
    gained −0.9 / −1.6 / −1.7% instructions and +0.3 / −6 / −12% peak heap
    on the placeholder versions of sym modules 21 / 25 / 63.
- **Stored contexts are non-display readbacks** (user's rule, commit
  `2096612e`).  Hole goals are re-evaluated and read back for display when
  printed.  The termctx thunk explicitly turns off `Displaying` and
  `Unifying`, because it may first be forced from inside either.  The
  termctx is forced only when actually needed, i.e. a let-only readback
  (`045c0dbf`): identity-environment checks use `Meta.tctx` instead.  This
  took `univalence.ny` from 143 forced contexts to 8.
- A solved unification meta is **always read back as its solution**
  (`Readback.unfold_solved`), because its environment mentions its whole
  context, which may not be in scope where it is read back.
- **Errors**: each unsolved meta reports `E2004` ("can't determine a value
  for this placeholder") at its own location, or a more specific code
  given at creation (e.g. for implicit boundaries).  Metas created together
  for one term (an expansion's fields, a boundary, a placeholder's type)
  share a location, and only the first error per location is shown.
  `echo` prints nothing while unsolved metas remain.

### Evaluation while unsolved

- An unsolved meta evaluates to a neutral whose lazy value is
  `Blocked_on (blocker, recipe)`.  A case tree stuck on it (a match on a
  blocked discriminee, or an application/projection/instantiation/action of
  a blocked neutral) evaluates to `Blocked b`, which is propagated.
- `force_eval`'s caching rule: once the blocker is solved, re-run the
  recipe and cache the result (a solution is permanent, see above).  While
  it is unsolved, stay blocked.  So values computed before a solution see
  it afterwards, without any invalidation pass.  This resolves the "cache
  invalidation landmine" from `EQUAL.md`, at least for `lazy_eval` refs.
- Deferred type actions (`gact_ty`) can find a `Realize` when a type was
  stuck on a meta that was solved after the type was normalized, and they
  act on the realized value.

### Speculation and the depth rule

**Soundness issue (found 2026-11-02).**  OCaml `Lazy.t` fields in values
(as opposed to the `lazy_eval` refs above) can memoize consequences of a
speculative solution that is later backtracked.  The fix is Lean's
mctx-depth idea: each unification meta records `Origin.speculation_depth ()`
at creation, and a speculation may solve **only metas created inside it**
(`Global.unif_assignable`, enforced in `solve_unif`).  When a speculation
succeeds, `Origin.on_speculation_success` lowers the depths of everything
created inside it.  Postponed constraints follow the same rule.

The user objected that this makes speculation incomplete.  The mitigation
agreed then was speculation-end trials, which would re-evaluate constraints
on outer metas as terms and solve them in a trial.  It was **dropped**,
because postponement (§6) made it mostly unnecessary and because we then
**removed most speculation from the checker**:

- Variable matches no longer use `Control.recovering`.  Index and parameter
  checks run in a plain `try` with a local `Wont_refine`, and branches are
  checked outside it (`859abc73`, `99d2af38`).
- Let-bound values no longer speculate about whether they are case trees.
  Syntactic `check_has_case_tree` / `synth_has_case_tree` decide this
  (`ca31b966`).
- Primary arguments decide between the old "given boundary" path and
  placeholder boundaries by a deep syntactic test (`synth_has_synth`, §3)
  instead of trying one and falling back.

What remains speculative is error recovery around type ascriptions
(`check_ascription`, `Asc` in `check_of_synth` / `synth`), trying the
alternatives of `First` / `SFirst` terms, and `calc`'s forward/reversed
attempts.  The user may remove `calc` and chose to leave it alone.  Inside
these, metas from outside can't be solved; whatever is stuck on them is
postponed instead.

Rollback must also clear caches keyed on physical identity: the hash-cons
table and the action memo (`Origin.on_backtrack`), and the memo of flexible
comparisons (§4).

## 3. Placeholders in the surface language

- `_` in term position → `Raw.Unif` → `make_unif` at the checking type.
- `Id _ a b` (only when the name written is the *type* name, the second
  of `refl_names`): a placeholder for a type, at
  `Id^k Type {_}… _ …`, with `k` counted from the explicit arguments.  This
  assumes full instantiation, and the user accepts partial instantiation as
  a known imperfection.  `refl _`, `ap _`, and superscripts stay `E0400`,
  since `refl _ x y` is ambiguous between `Id` and `ap`, and a
  higher-dimensional universe placeholder can't be applied.
- `sym _` is a unif at the inverse-permuted type.
- A **nonsynthesizing primary argument with implicit boundaries** gets
  placeholder boundaries (`TakenArgs.Placeholders` in `synth_arg_cube`),
  for both instantiation and application.  To avoid changing ordinary code,
  a deep syntactic test (`Check.synth_has_synth`) dispatches irrevocably:
  if the primary has all the synthesizing subterms it needs, the old
  "given" path is used, otherwise placeholders.  Removing the old path
  entirely was tried: `univalence.ny` went from 0.12s to 0.41–0.58s after
  fixes, the overhead remained undiagnosed, and one error message got worse.
  The user wants full subsumption noted for **later**, since it would also
  remove the old path's double elaboration of the primary.
- `match M return _`: a non-dependent match without counting index
  variables.  This is the explicit non-refining form suggested by `E1103`
  messages.  It is also on its own branch `match-return-placeholder` for
  master.
- **Not yet**: implicit arguments.  `ImplicitApp` / `ImplicitSApp` will be
  removed once they exist, so no work goes into supporting them.  A general
  `_ : _` rule for all synthesizing positions was tried before postponement
  existed and dropped.

## 4. Equality with metavariables (`equal.ml`)

**Three outcomes.**  `failure = Unequal of Unequal.t | Stuck of Unequal.t * blocker list`.
`Stuck` keeps the local mismatch so messages are unchanged if it is never
decided.  It arises when a spine isn't forced (below) and in
`equal_at_data`'s constructor-vs-neutral case, with blockers from
`stuck_on`: the blocker of each value plus shallowly blocked arguments.
The blocker list is **not complete** (metas inside a meta's environment are
ignored), so the end-of-command loop also retries every constraint if
anything at all was solved since its last attempt.  `Stuck`
short-circuits like `Unequal`, because later comparisons might be
ill-typed.

**The solver hook.**  `with_solver ctx x y ty` runs at the top of
`equal_at` and `equal_val`.  `Equal.solver` is a forward reference
installed by `Unify` (which needs readback) and returns
`Not_solved | Solved of unit Err.t | Impossible`.  The solver tries, in
order: solve `x` directly, solve `y` directly, expand `x`, expand `y`
(direct solutions are preferred over expansion).  `Impossible` means "no
solution of this meta makes them equal, however other metas are solved",
and turns a subsequent `Stuck` result into `Unequal`, so rigidly unsolvable
problems get the pre-postponement error messages.

**Flexible spine comparison (smalltt's flex mode).**  Two same-head neutral
spines may fail to match and then become equal after unfolding: if `g`
ignores its arguments, `g ?v b1 = g a1 b2` holds and says nothing about
`?v`.  So spines are first compared **flexibly**, i.e. without solving
(`Equal.flexible`, `flexibly`).  `equal_neu_or_unfold` then does the
following:

1. Compare spines flexibly.  On success, done.
2. Otherwise, if either side unfolds (`view_term` changes it), retry on the
   unfoldings (once per node, as in `EQUAL.md`).
3. Otherwise, if both spines are **forced** (`forces_spine`: the head is
   not a meta, and the value is `Unrealized` or a `Canonical` type, i.e.
   permanently stuck or generative), compare them again *with* solving.
4. Otherwise, the comparison is stuck, except that the **instantiation
   arguments** of types are compared, with their types, since they are
   generative even when the head isn't.  This solves `?X` in
   `Id ?X ?x ?y =? Id A a b`, after which the comparison is retried, and
   finally the uninstantiated types are compared (`Readback.uninstantiate`),
   so `?F x y =? Id A a b` solves `?F := Id A`.  The user confirmed that
   `Id` and `refl` are injective.

`equal_at_eta_spines` never solves, since its fallback (eta-expansion) is
complete anyway.  Unfoldings at a datatype go back through `equal_at`
rather than `equal_at_data`, so the solver sees a meta exposed by unfolding
(`fabf5ae9`).  `equal_head` compares a meta's permutation (as it already
did for constants), so `?m =? sym ?m` no longer passes trivially, and the
same fix applies to holes.

**Flexibly-stuck rule** (`0cc7fce0`).  In flexible mode, a value headed by
an unsolved unif meta can't become equal to one not headed by the same
meta, so `equal_at` returns `Stuck` immediately instead of eta-expanding
and unfolding the other side, which could be very expensive only to get
stuck anyway.  The exception is a record type with no fields, where
eta-expansion would succeed; testing for all singleton types instead cost
too much.  This fixed an OOM and cut the benchmark by up to 7% of
instructions and 18% of heap.

**Memo of flexible comparisons** (`d90c0589`, `5f2dddf0`).  After a failed
flexible attempt, the solving redo compares the arguments again, and each
argument starts with its own flexible spine comparison, which the outer
attempt already did.  With deep unfolding chains this was quadratic
(1.6M calls versus 219 in one case).  So within one external comparison,
`equal_spines_flexibly` remembers results keyed physically on `(mode, x, y)`
with a shallow whole-spine hash (a head-only hash put 6206 entries in one
bucket), buckets capped at 8, and the memo reset when `Global.solve_count`
changes or a speculation is backtracked.  The soundness argument, which the
user asked to be right for modal code too, is in the comment in
`equal.ml`: the context enters only through its length, mode, and locks
that are used only after value-based decisions.  The memo is skipped when
there are no unsolved unifs.  Keeping `Ok`/`Unequal` entries across solves
was measured and not adopted, because there were too few extra hits.

## 5. The solver (`unify.ml`, `readback.ml`)

### 5.1 Direct solution

`try_solve_direct ctx u v ty`: `u` must be a neutral headed by an unsolved,
assignable, non-delayed unif meta with identity insertion and an
argument-only spine, and `v` must not be the same meta.  If the comparison
type is unknown, the types of `u` and `v` are compared first.  Then:

1. `renamed_ctx` checks that the environment and arguments form a renaming
   and builds the **renamed context**: the shape of the meta's context, but
   with each variable at the level of its image in the current context, so
   it acts as the inverse substitution.  No evaluation and no termctx are
   needed.  The arguments become further entries, and the solution is an
   abstraction over them (`wrap`).
2. Try eta-contracted solutions first (`contracted`): `?f y =? g y` gives
   `?f := g`.  This is done only when nothing is undefined, since otherwise
   it changes the problem: `?f x x =? g x` has no MGU but `?f x =? g` does.
   It also requires `same_arg` (same cube and application dimensions, same
   modality, no key).
3. Otherwise, `readback_unif_solution` reads `v` back at `u`'s type in the
   renamed context in `Unifying` mode, which raises
   `Unsolvable (Rigid | Flexible)`.

**`Unifying` readback** (a dynamically scoped ref rather than a reader
effect, for speed; it is a no-op outside solving):

- *Scope*: a variable outside the image is a **rigid** failure.  An
  *undefined* variable (one with several preimages or a mismatched
  annotation) is **flexible**.  A variable whose type mentions an undefined
  variable is itself undefined (a cascade through the types, read back
  after menv substitution), and the meta's own type is checked the same way
  (`check_type`).  Undefined bindings hold a `Failed` value, so a physical
  identity check can't read `β[y,y]` as a bare `β`.
- *Occurs*: the target occurring strictly inside a rigid neutral or a
  constructor argument (`under_rigid`) is rigid.  At the top, under
  lambdas, tuples, or permutations, it is flexible, since `?m =? sym ?m` has
  symmetric solutions, and eta.
- *Unfolding*: solved unifs and the current command's valued `Def` metas
  are unfolded.  A neutral blocked on another meta, unfoldable values, a
  singleton type (via the `Readback.singleton` hook), locks, and the type
  check are all *flexible* frames, i.e. not rigid.
- *Rigid* failures make the solver return `Impossible` (§4).

### 5.2 Permutations

`sym ?m =? t` and `(sym ?f) x⃗ =? t` are solved by acting on both sides with
the inverse permutation (`try_solve`, `inverse_of_spine`: undo the
outermost insertion, then the rest extended by identity, so
`(sym ?F) x⃗` becomes `?F (sym x⃗)`).  Inside environments and arguments, a
permutation of a plain variable counts as a renaming entry.  Its binding's
value is the permuted variable, and `renamed_deg` composes the inverse with
the occurrence's degeneracy.  Repeated variables are counted by level,
whatever their permutation.

### 5.3 Keys and prekeys (modal environments)

The image of a variable can carry a key, and the environment can contain
**prekeys** (e.g. a counit after projecting a modal field, or a key on a
closure's environment) acting on everything below them.  Then an occurrence
`y⟨κ⟩` in `v` must be read back as `x⟨κ'⟩` for the `κ'` that the prekeys
send to `κ`.  The formula, worked out and verified by the user:

> image of `x⟨k⟩` under σ = `P_θ ∘ k ∘ Q ∘ κ₀`

where `P` is what `restrict_keys` collects from the locks to the right of
`x`, prewhiskered by the locks added during readback; `Q` is what
`lookup_cube` collects on the way down (prewhiskered by `x`'s annotation);
and `κ₀` is the entry's own key.  Through modal fields this becomes
`P_θ ∘ c ∘ (Q⋆g) ∘ κ₀`, with `c` obtained from `k` by `c ↦ ε ∘ (c⋆g)` per
field, by the triangle identities.  A candidate is accepted iff
`Modalcell.compare` equals the occurrence's key, using `acts_as`, which
compares up to postwhiskering because acting by a cell is the same as
acting by any postwhiskering of it.  The user's requirement is that
`Modalcell.compare` respects the triangle identities in every mode theory;
if it doesn't, that's a mode-theory bug.

**Choosing `κ'` and preimages needs cell enumeration.**  To stay MGU we need
"exactly one fitting candidate", not "some candidate".  So every mode
theory now provides `find_all` (`Some l` = `l` is *all* the cells, `None` =
no claim), and `find_unique` was made **honest** (`Some` means *exactly
one*).  `Readback` keys use a three-valued `'a fit = Unique_fit | No_fit |
Unclear_fit`.  A cctx variable with several preimages gets `candidates`
(renamed variable / inverted leaf / opaque), and `resolve_candidate`
chooses the one that fits the occurrence: any `Unclear` means flexible
failure, otherwise there must be exactly one `Unique_fit`.  Lesson
learned: deriving `find_all` from a dishonest `find_unique` produced a
real non-MGU solution in `-ambiflector` (`End(id) = {id, zero}`), and
auditing found the same lie in `-ambiflection`.  This work also exposed
and fixed completeness/compare bugs in the reflector/coreflector and gwpt
mode theories, and introduced the white-box closure test
`test/white/modal_closure.ml`.  It all lives on separate branches for
master (`reflector-completeness`, `gwpt-completeness`, `honest-find-unique`,
`enumerate-cells`, `nested-key-display`), merged into `unif-metas`.

### 5.4 Inverting tuples and abstractions in environments

A variable of the meta's context (or an argument) may be sent to a value
built from eta-record **tuples** and **abstractions** whose leaves are
variables applied to exactly the bound variables, in any order: `(y, z)`,
`w ↦ y w`, `w ↦ (y w, z w)`, `u v ↦ y v u`, and higher-dimensional
versions.  Every such value is the eta-expansion of the variable applied to
the inverse, so substitution still discards nothing (`invert_value`).  The
inverted variable gets a fresh level, and each leaf gets an `inversion`
path (`Proj` / `Mproj` / `Apply (position, modality)`, plus an inverse
permutation and prekeys) in a table consulted by readback.  Readback of an
inverted leaf is **value-based**: it computes the projections on `x`'s
value, acts by the occurrence's degeneracy and the key that its key
induces (`key_before`), then applies/projects and reads back
(`readback_inverted_head` / `_apps`).  Supported:

- **cubes**: each face is a separate variable, inverted at its own type,
  and leaves must be applied to whole cubes;
- leaves that are **permutations**, including under abstractions;
- **proper degeneracies** (`refl`) on occurrences of applied leaves;
- **modal** entries, functions, and fields, including **modal fields inside
  abstractions** (the leaf applies the bound variable through the unit with
  modality `ν;ℓ`, i.e. the transpose of the identity);
- all of the above **under prekeys**, and **keyed entries/leaves**;
- under-applied leaves, eta-expanded only as far as needed.

Mismatched dimensions are **refused**: at arity 0, face lists don't
determine cube dimension, so `(x ↦ f x) : (x : Id A .) →⁽ᵉ⁾ Id B .` must not
invert to `f`.  This could be supported by recording the binder's dimension
on `Apply`.

Eta-short readback of a tuple equal to an inverted variable's value (giving
`g p` instead of `g (p.1, p.2)`) was **dropped by the user**: a tuple has
many possible types (nominal records, phantom parameters, fieldless
records).

### 5.5 Not in the fragment

- **Variable matches.**  In a branch, the environment let-binds the match
  variable to a constructor.  Solutions are not unique there, so this
  needs postponement (it gets it, §6).  Pruning would *not* help.  A
  regression showed that `renamed_ctx`'s fast path had to check
  `is_identity_ordered_env` against the meta's own context, otherwise it
  accepted such an environment and produced a non-MGU solution
  (`de8c4781`).
- **Pruning** is deferred until implicit arguments exist, in case it
  becomes more useful then.  A measurement found that at most 17% of
  retried benchmark failures had a prunable occurrence, which is an upper
  bound on what pruning could rescue.
- **Flex-flex** is handled only partly.  `?f σ =? ?g τ` with different
  metas is solved when one side's environment and arguments are a renaming
  whose image contains everything the other side uses: `flexflex` in
  `unif.t` solves `f := g`.  Two cases are not handled.  The first is the
  same meta with different renamings, `?m σ =? ?m τ`.  The solver leaves
  it alone, the environments are compared structurally, and if they differ
  the comparison is stuck.  The pattern-unification answer is
  `?m := ?m' restricted to the variables where σ and τ agree`.  The second
  is different metas where neither side's scope contains the other's.  The
  answer there is a fresh meta over the intersection of the scopes, which
  needs pruning machinery.
- Constructors, non-identity degeneracies of applied variables, blocked
  entries, and rigid neutrals in environments (§1).

### 5.6 Expansion (eta for metas, on demand)

Metas are **not** eta-expanded at creation.  Instead:

- **Projection** (`try_expand`): `?m x⃗ .fld =? t` needs `?m` to be a
  tuple.  This is MGU by eta, but creates metas, so it is done only on
  demand.  Rather than duplicating tuple checking (modal fields live in
  locked contexts and maybe other modes), the solver builds a *raw term* of
  abstractions, tuples, permutations, and `_`, and runs the ordinary
  checker at the meta's type (`Check` installs `Unify.expander`).
  Expansion typechecks in the middle of a comparison, so it runs under
  `Global.without_retries`.  Permuted occurrences (`sym ?m .fld`) expand to
  the inverse permutation of a tuple.
- **Constructor boundaries** (`refine_to_constr`): a constructor checks at
  a higher datatype only if its boundary consists of the same constructor.
  So a meta there with a renaming environment is refined to that
  constructor applied to fresh metas; this is MGU, since a renaming can't
  produce a constructor otherwise.  Non-renamings remain `E1002`.
- **Singletons** (`solve_singletons`, run by `settle_unifs` and before
  `echo`): an unconstrained meta whose type is a singleton (two fresh
  variables are equal flexibly) is expanded one layer, repeatedly.  Later
  fields can't depend on earlier ones' values, since those are singletons
  too.  Symmetrized records (non-identity insertion) expand as a
  permutation of a tuple.

## 6. Postponement

Agreed **why**: a term whose correctness depends on an undecided equation
must not be evaluated (ill-typed evaluation can crash or diverge), but it
should start evaluating as soon as the equation is solved.

- **Delayed metavariables** are the vehicle: a unif meta with
  `delayed = true` is not assignable by unification, only *released* by a
  stored action, and it is `Failed` if its constraint fails.  Because it
  evaluates as `Blocked_on` like any unsolved meta, computations involving
  it are redone on release.  The user agreed metas are the right vehicle.
  - **Guarded constants** (Agda's pattern): `check_synthesized` elaborates
    `t : S`, and if `S ≤ T` is stuck it returns a delayed meta at `T` and
    postpones the comparison, releasing `t` when it holds.  It is used by
    `check_of_synth`, its `Asc` case, `App` in checking position, checking
    `Act`, `check_constr`'s output type, `check_letonly_term`, and
    `synth_arg_cube`'s given boundary.
  - **Postponed problems** (`postpone_problem`): the type is stuck, e.g.
    checking `x ↦ b` at `?T` (lambda, tuple, constructor, numeral at a
    blocked type: `E0407`), applying a function of blocked type (`E0408`),
    or projecting from a blocked record type (`E0409`).  The stored problem
    re-runs under the original location, meta owner, and positivity scope.
    Synthesizing cases create an ordinary (silent) result-type meta and run
    `check_synthesized` against it on retry.
  - **Validations** (`Check.validate`, no guard): a stuck check of
    something that doesn't affect the elaborated term (an ascribed lambda
    domain, an explicit constructor boundary `E1005`) is just postponed.
  - Delayed metas display as `?uN` with a located remark "?uN stands for
    this term, whose type hasn't been checked yet".  The user rejected
    displaying the guarded term itself, because it gives misleading "x vs x"
    messages.
- **Constraints** (`Global.Postponed`): closures `attempt : unit -> Done |
  Stuck blockers` and `report`, plus blockers, `seen` (the solve count at
  the last attempt), and depth.
- **Retry only at safe points**, never re-entrantly inside `Equal` or
  readback, and only at the creating speculation depth: `Check.retrying`
  (re-compare if stuck after `retry_postponed`) at comparison sites,
  `retry_if_stuck` before *decisions* that treat stuck as failure (match
  branches, variable match, refutation, emptiness, lambda/comatch/tuple
  views), and at the end of the command and before `echo`, where
  `settle_unifs` loops retry → stale retry (anything solved since `seen`)
  → singletons until nothing changes.
- **Leftovers** at the end of a command: `E0406` (and friends `E0710`,
  `E1005`) plus the `E2004`s of their placeholders.  Constraints stuck only
  on delayed metas are skipped as consequences of other errors.  There is
  no defaulting.  Subtyping is currently empty in practice (no UI for
  `Subtype.add`), and the user intends to deal with more general subtyping
  when it arrives.
- **Decisions never postpone**, and must not depend on solving order:
  - Variable match: woken constraints are retried first; a stuck index is
    `E1103` (unless another index rigidly prevents refining, which falls
    back to the old behaviour).  Parameters that mention index variables
    only inside blocked neutrals → refine optimistically, plus a postponed
    independence check (`E1104`), via `Readback.with_blocked_dependence`.
    Messages suggest `return _` or more explicit arguments.  The user is
    content with `return _` as the explicit non-refining form.
  - `check_letonly_type`, the higher-function domain boundary, and
    `InstHigherPi` boundaries are also decisions that don't postpone.
- **Granularity**: the whole problem is retried; constraints are not split.
- **Occurrence analysis**: postponed problems record `Recursive`
  conservatively.  That is harmless while window transparency is the only
  consumer.  The agreed direction, once positivity/termination checking
  exists, is an end-of-command pass over the fully elaborated definition
  (as Agda/Lean/Rocq do), with window-transparency checks becoming
  constraints decided after it.

## 7. Error messages and display

Unification made error messages much more expensive: speculative messages
are formatted but never shown, and placeholders produce huge normal forms.
Related changes, also on separate branches for master:

- `Equal` builds head-mismatch printables lazily (`PHead`, `5739472c`).
  Reading back a meta head eagerly had been 38% of the time.
- **Folded error messages** (user's decision, `6026da45`): values in
  messages are read back without unfolding glued neutrals, except
  internal `Def` / `Unif` metas.  Holes, `echo`, and annotations stay
  normalized.
- **Display budget** (`10852ad0`, `display size`, default 2000 subterms):
  the budget bounds output nodes, but *not* the evaluation that display
  readback forces.
- Nested keys are displayed according to their composite (`4f052f5e`).

## 8. Performance

**Benchmark** (untracked `bench-unif/`): symmetry-narya with every argument
that occurs in a later parameter's type replaced by `_`, through module 77.
5731 of 7712 replacements check.  Always measure with
`-source-only -no-write-compiled` (otherwise `.nyo` rewriting adds 0.5–1%
noise), using `perf stat -e instructions:u` (needs
`kernel.perf_event_paranoid=1`) and peak heap from `OCAMLRUNPARAM=v=0x400`,
with `ulimit -v` + `timeout`, and check stderr for `error[`.

**Cost on ordinary code**: none measurable.  The `metavariables` branch is
about 5% faster than master, and the unification machinery costs within
±1% (`Unifying` as a ref rather than an effect, flexible mode and the memo
skipped when no unifs are unsolved).

**Cost of placeholders**: about 2.0× instructions / 5× heap at first
(module 63).  The overhead was concentrated in a few definitions, where a
meta in a non-generative spine forces unfolding and solutions are found
deep inside unfoldings.  After the fixes below it is about 1.5× / 1.6×,
and lower since the flexibly-stuck rule.  We agreed that about 2× is an
upper bound on the *inherent* cost of the MGU policy (other systems pay
too, or give up MGU).  We chase our own inefficiencies, not the policy.

*Adopted*: writing solutions into cells at solve time (§2); hash-consing of neutrals built by variables/application/
projection plus a memo of degeneracy actions on neutrals (the biggest
single win: hott.t −38%, placeholder heap down 5×; branch `hashcons`); the
flexible-comparison memo; the flexibly-stuck rule; lazy `PHead`; forcing
termctxs only for let-only readback; the `renamed_ctx` identity fast path
restricted to the meta's own context; prekey composition dropping
identities (`909e216e`).

*Measured and rejected*:

- a general comparison memo (pays only together with `glued_view`);
- `glued_view` (keeping glued neutrals through `apply` / `field` for better
  solutions: exponential re-comparison in nested spine attempts);
- a Π-evaluation memo;
- an attempt-depth limit;
- ONESTEP lazy delta (unfold one level for same-constant heads: worse
  everywhere);
- NOFLEXUNFOLD (don't unfold in flexible mode: the blowup moves to the
  fallback);
- `act (act x s) t` coalescing (≤0.4% of calls);
- caching speculative `force_eval` results on their own (about 1%;
  superseded by writing cells at solve time, which removed speculative
  solutions altogether).

*Remaining slow cases* are all placeholders that genuinely can't be
inferred, so they error either way.  The time goes to unfolding in
comparisons stuck only on the placeholder, and to normalization during
display.  The user's position is to skip a work budget for now: "wait to
see what actually bites users".  Untried directions: real lazy delta
(definitional-height order), or postponing such comparisons instead of
unfolding them.

## 9. Open points

Next (user's plan): **implicit arguments**, in a new session, and then
remove `ImplicitApp` / `ImplicitSApp`.  Implicits may make performance
matter more.

Deferred or not started:

- **Docs**: `_`, `Id _`, `return _`, postponement, and the new error
  codes (E0406–E0409, E0710, E1005, E1103, E1104, E2004) are not in
  `docs/`.  To be written after implicits.
- **Solver fragment**: pruning (waiting for implicit arguments); flex-flex
  with the same meta (intersection) or incomparable scopes; non-renaming constructors in boundaries
  (E1002); arity-0 inversion at mismatched dimensions; rigid-vs-flexible classification for exhaustively-empty candidate lists.
- **Postponement**: constraint splitting; postponed matches (only needed
  when the *head* of the discriminee's type is unknown; kinetic position
  with a variable discriminee is easy, case-tree positions need potential
  delayed metas); degeneracies (`Act`) at stuck types; problems in
  case-tree positions; subtype-aware solving (a meta against a constant
  with declared subs/supers should postpone, not solve by equality); the
  end-of-command occurrence analysis.
- **Elaboration**: full subsumption of the "given boundary" path by
  placeholders; `Id (Id _) _ _ _ _` (implicit boundaries still need a
  synthesizing primary).
- **Mode theories**: the constants check uses "some key exists", which is
  the user's reasonable guess; nonparametric constants are deprecated, and
  the right condition is unclear.
- **Performance**: a work budget, lazy delta, extending the benchmark
  (modules 64–77 could keep many more placeholders; module 78 may now fit),
  and the module-60/68/72/76 slow cases.
