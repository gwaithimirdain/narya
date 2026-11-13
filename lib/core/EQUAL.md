# Notes on equality-checking: design, history, and future unification

This file records the design rationale for the equality/conversion checker in
`equal.ml` as restructured in July 2026 (commits `6f260aa1`, `aa472ae8`,
`5b7cd519`, on top of the glued-evaluation repairs `a017a3cd`, `5d55666e`,
`e4c38209`, `a355dd0d`, `e31b5e4d`), its relationship to smalltt's
"approximate conversion checking" (https://github.com/AndrasKovacs/smalltt),
which the previous design was modeled on, and the considerations for
adding unification that were anticipated beforehand (unification itself is
documented in `UNIFY.md`).  (Glued evaluation has since been made permanent: the
`GluedEval` toggle in `value.ml` and the eager-evaluation code paths it
guarded have been removed.)

## Current design

Equality is typed and eta-directed (`equal_at` dispatches on the view of the
type), with the following performance-critical structure:

1. **Pointer equality first** (`aa472ae8`): `equal_at` and `equal_val` return
   success immediately when the two values are physically equal.  Physically
   equal values are definitionally equal, so this is sound; it is important
   because glued evaluation shares aggressively (cached constants, shared
   let-bound metavariables, forced results cached in shared `lazy_eval` refs),
   and without this check the same objects are re-compared structurally over
   and over, each comparison eta-expanding through records and function types.
   Measured on `equiv_triangle_to_Id_map` in the MURI tutorial file: 2.47M
   spine comparisons of which 59 failed, i.e. essentially all comparison work
   was redundant; this check took that definition from 138s to 0.44s.

2. **Spine equality before eta-expansion at eta types** (`5b7cd519`,
   `equal_at_eta_spines`): at a pi-type or eta-record type, if both sides are
   neutral, first try comparing their spines rigidly.  Success is conclusive
   (equal spines imply equal values).  A mismatch is *inconclusive* under eta
   (different spines can be eta-equal), so on mismatch we fall back to the
   eta-expanding comparison as before; a spine mismatch must never be reported
   as inequality here.  This matters most with glued evaluation, where
   parallel derivations of the same value produce equal retained spines that
   are *not* physically shared, so check (1) misses; without this check the
   eta-expansion compared their unfolded realizations recursively, with the
   fresh variables introduced at each level defeating sharing below.  Measured
   on the conversion at the heart of `retract_Id_Equiv` (checking
   `fiber A B ((ua_equiv A B e).trr) b.0` against
   `Σ A (a ↦ Id B (e .fst a) b.0)` under a 1-dimensional binder): eager
   evaluation performed 156 pi-type eta-expansions in this conversion; glued
   evaluation performed 346,000+ and did not finish in ten minutes.  With this
   check the conversion is essentially free, and the whole tutorial file went
   from >20min (glued) / 2.5min and ~19GB (eager) to 0.6s and 49MB (glued).

3. **Local unfolding on demand** (`6f260aa1`): comparing two neutrals
   (`equal_val`, or `equal_at`'s datatype case, where unfolding can produce
   constructors), we first compare their spines rigidly (`equal_neu`).  On a
   spine mismatch we view both sides with `view_term` — which, under glued
   evaluation, forces the stored value and unfolds `Realize` chains all the
   way down — and retry *at this node only* if either side physically changed.
   Since a second view is the physical identity, there is at most one
   unfolding retry per node, and subterms whose spines match are never
   unfolded.  Any spine mismatch must fall through to unfolding before being
   reported, because equal-length spines with a shared *non-injective* head do
   not determine inequality.

Ordering invariant (long-standing, worth preserving): `equal_apps` starts
each case with its recursive call, so spines are processed by first comparing
only type-agnostic structure on the way in (spine shape and modality
annotations, which are needed to build the locked contexts), then the *heads*
at the bottom, then insertions/arguments/fields on the way out, innermost
(leftmost) first.  Heads must be compared before any arguments: equality of
heads *concludes* equality of their types, and the argument comparisons assume
they are comparing at a common type.  This also means the `Dimension_mismatch`
anomaly in the `Arg` case is unreachable when comparing two arbitrary neutrals
(as `equal_at_eta_spines` does): unequal heads produce an ordinary `Error`
before any argument or dimension comparison is reached.

## History: the Rigid/Full two-pass design, and why it was replaced

The previous design ran every equality problem under a reader effect
`Mode ∈ {Rigid, Full}`: first the *whole* problem in Rigid (no unfolding
anywhere: glued neutrals compared purely as spines), and if that failed
anywhere, the *whole* problem again in Full (with `view_term` applied at every
node, i.e. unfold everything).  This was modeled on smalltt's approximate
conversion checking, but coarsened it in two ways that turned out to be
load-bearing (see below), and combined with the typed eta-first `equal_at` it
meant that in practice every sizable conversion ran twice, with the second run
being the expensive unfold-everything pass — so the glued spines' benefit was
almost never realized (~25% overhead on hott.t/sigma2.ny, catastrophic on
ua/glue-heavy files).

Side effects of the removal, for the record: `equal_apps`/`equal_tyargs` now
propagate structured `Some (Error _)` reasons instead of squashing them to
`None` (so some error messages became more specific, toggle-independently),
and a latent guard in `subtype.ml` that treated any `Some` result of
`equal_tyargs` as success was fixed at the same time.

## Comparison with smalltt

What smalltt actually does (README, "approximate conversion checking"): three
unification states, with speculation scoped to a single same-head pair.

- **Rigid** (ambient): normal unification; on-demand unfolding and meta
  solutions allowed.  On identical defined heads, attempt spine unification
  in Flex.
- **Flex** (speculative): no unfolding, no meta solutions; succeeds or aborts
  inconclusively the moment anything would require unfolding.
- **Full**: entered when a Flex attempt fails: unfold both sides *of that
  pair* and finish *that subproblem* with everything unfolded and no further
  speculation.

Their linearity guarantee is "backtracks at most once on any path leading to
a subterm": one speculation per location, and a failed speculation dooms only
its own subtree to Full, while siblings and ancestors continue in Rigid and
keep speculating.

The old Narya design diverged in three ways:

1. **Speculation scope was global.**  Narya's `Rigid` pass was smalltt's
   *Flex* — no unfolding at all — applied to the entire problem as one giant
   speculation.  smalltt never runs a whole problem in Flex.
2. **The fallback scope was global.**  One inconclusive leaf rethrew the
   entire toplevel problem into Full, discarding completed sub-comparisons and
   unfolding even at subterms whose spines would have matched.  In smalltt a
   failed speculation Full-izes one subtree only.
3. **Typed eta-first comparison denied spines their role.**  smalltt's
   conversion is syntax-directed: two neutrals at function type are compared
   spine-first, with eta entering only for Lam-vs-neutral mismatches.  Narya's
   `equal_at` eta-expanded unconditionally at pi and eta-record types — in
   *both* modes — so the no-unfold spine comparison never got a chance exactly
   where it mattered.  Empirically this was the largest factor (the 2200×
   eta-expansion ratio above).  `equal_at_eta_spines` restores the
   spine-first behavior inside the typed checker.

The current scheme is deliberately not identical to smalltt either:

- Our speculative spine comparison is *definitive* rather than abortive:
  comparing `f x ~ f y`, the inner `x ~ y` is settled completely (with local
  unfolding of `x`,`y` if needed) rather than aborting at the first need to
  unfold.  When `x ~ y` holds only after unfolding, smalltt aborts the Flex
  attempt and unfolds **f** in Full; we unfold only `x`,`y`, the outer spines
  then match, and the outer head is never unfolded.  Preserving outer spines
  harder than smalltt does is the right bias here, both for readback size and
  (later) for meta-solution quality.
- The once-per-node bound is enforced differently: `view_term` collapses the
  whole `Realize` chain at once, caching in the shared ref, and the retry
  fires only if a view physically changed something; redundant re-comparisons
  are absorbed by the pointer shortcut.  smalltt needs neither because its
  speculations are cheap; see the cost model below.
- There is no Flex state because there is nothing for it to protect: without
  metavariables in the checker, speculation cannot commit wrong solutions,
  and inconclusiveness can always be resolved definitively by unfolding.
  (The old design's two-state reduction of smalltt dropped Flex correctly —
  but kept the global two-pass shape, whose justification in smalltt depends
  on the per-path scoping that was dropped along with it.)  This was
  written before unification; with unification metavariables a Flex state
  does now exist (`Equal.flexible`), scoped to individual same-head spine
  comparisons as in smalltt; see the last section and `UNIFY.md`.

## Why the cost-benefit differs from smalltt

smalltt's object language is pi, universes, top-level definitions, and metas —
no records, no datatypes, no dimensions.  A comparison node there costs almost
nothing and unfolding is the only expensive operation, so even crude retry
policies are affordable.  In Narya a comparison node is expensive by itself:
eta-expansion manufactures fresh variables and evaluates bodies, record
comparison pays `tyof_field` per field, everything carries boundary tubes, and
degeneracy actions on retained spines walk argument-type towers.
Consequently:

1. whole-problem restarts are amplified by orders of magnitude;
2. *avoiding eta-expansion* is worth more than avoiding unfolding — the
   reverse of smalltt's priorities; and
3. "unfolding" under glued evaluation means forcing deferred evaluation
   chains, whose cost is itself nontrivial (and whose results should be
   shared: hence the importance of forcing caches in shared refs, the
   constant-evaluation cache, and the pointer shortcut).

## Unification: what was anticipated, and what happened

This section was written before unification existed, as a list of things
to keep in mind.  Unification has since been implemented on the
`unif-metas` branch; see `UNIFY.md` for the full design.  Each
consideration and how it turned out:

- **Results become ternary.**  Yes: `failure = Unequal | Stuck of _ *
  blockers`.  `equal_neu` did become the speculative spine comparison (run
  "flexibly", i.e. without solving), and the local retry points in
  `equal_neu_or_unfold` are where solving re-enters: after a failed
  flexible attempt, unfold if possible, otherwise re-compare *with* solving
  only if both spines are forced (permanently stuck or generative heads),
  otherwise report `Stuck`.
- **Speculation must not commit meta solutions.**  At the level of
  `Equal`, flexible mode never solves.  At the level of the typechecker's
  speculations (`Origin.speculate`), trailing turned out to be insufficient,
  because OCaml `Lazy.t` fields can memoize consequences of a backtracked
  solution.  So a speculation may only solve metas created inside it (the
  depth rule), and most speculation was removed from the checker.
- **Fallback strictness.**  We kept the definitive local scheme.  Stricter
  smalltt-style variants (spine attempts that never unfold, an
  attempt-depth limit, one-step lazy delta, no unfolding in flexible mode)
  were all tried on the placeholder benchmark and made things worse
  somewhere.  The quadratic re-comparison that metas introduce is handled
  instead by a memo of flexible spine comparisons within one external
  comparison, plus the "flexibly stuck" rule (in flexible mode, a value
  headed by an unsolved meta is stuck at once rather than eta-expanded).
- **Glued spines improve solution quality.**  True, but preserving *more*
  glue (keeping glued neutrals through `apply` / `field`, "glued_view") made
  the spine-attempt-then-unfold cost model exponential on real code, even
  with hash-consing and a comparison memo, so it was reverted.  Solutions
  are read back from whatever glue evaluation already preserves.
- **Cache invalidation landmine.**  Resolved for `lazy_eval` refs by
  `Blocked_on (blocker, recipe)` states: a result that was blocked on a
  meta is recomputed and cached once the meta is solved.  (At first a
  solution was only permanent once written at the end of the command, so
  there was also an uncached "speculative" state.  The depth rule above
  made solutions permanent at once, and now they are written at solve
  time.)  `Lazy.t`
  fields are handled by the depth rule above.  Physically keyed caches
  (hash-consing, the action memo, the flexible-comparison memo) are reset on
  backtracking, and the latter also whenever a meta is solved.
- **Pointer equality** remains sound and remains the first check.  The
  "comparing-then-solving race" for pair-keyed caches was real: the
  flexible-comparison memo is stamped by a solve counter (and reset on
  backtrack, since the counter is itself speculable and can return to an
  old value with different solutions).

## Benchmarks used in this work

`test/black/hott.t` (especially `pi2.ny`, `sigma2.ny`, `glue2.ny`) and the
2025 MURI tutorial file (`veryslow.ny` in the repo root at the time of
writing; univalence from quasi-invertibility via `glue`, ending with
`retract_Id_Equiv`, whose final `is_contr` conversion under a 1-dimensional
binder was the stress test for all of the above).  Useful diagnostics, both
temporary code, described in more detail in the commit messages: counters on
`eval` / `apply` / `field` / `tyof_*` / `act` / `equal_*` /
eta-expansion sites keyed by an environment variable, and a SIGVTALRM
folded-stack sampler with periodic dump.  The single most informative signal
was comparing counter profiles between glued and eager runs of the *same*
conversion: gross asymmetries (evaluations, eta-expansions) point directly at
the missing sharing or missing fast path.
