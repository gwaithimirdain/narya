# Notes on equality-checking: design, history, and future unification

This file records the design rationale for the equality/conversion checker in
`equal.ml` as restructured in July 2026 (commits `6f260aa1`, `aa472ae8`,
`5b7cd519`, on top of the glued-evaluation repairs `a017a3cd`, `5d55666e`,
`e4c38209`, `a355dd0d`, `e31b5e4d`), its relationship to smalltt's
"approximate conversion checking" (https://github.com/AndrasKovacs/smalltt),
which the previous design was modeled on, and considerations for adding
unification later.

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
   not determine inequality.  With glued evaluation off, `view_term` is the
   identity and the comparison logic is unchanged.

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
  on the per-path scoping that was dropped along with it.)

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

## Considerations for future unification

When metavariable solving is added to the checker:

- **Results become ternary**: equal / unequal / *blocked* (on an unsolved
  meta).  The local-unfolding structure accommodates this naturally:
  `equal_neu` is already exactly the "speculative spine comparison" and would
  grow a speculation flag (no meta solutions; return Blocked on meta heads);
  the local retry points in `equal_val` and `equal_at`'s datatype case are
  exactly where the Rigid→Full transition lives.
- **Speculation must not commit meta solutions** (or must trail and retract
  them).  Solutions are committed only outside speculative attempts.
- **Fallback strictness becomes a real choice.**  Currently, after unfolding
  at a node we re-enter the same speculative strategy on the unfoldings; with
  metas, failed speculations can be retried after each meta solution, so the
  cost model shifts back toward smalltt's stricter "no further speculation
  below a failed one" bound.  Keep this as an explicit knob rather than an
  accident of structure.
- **Glued spines improve solution quality.**  Eta-short, unfold-free meta
  solutions (which smalltt prizes) are read back from exactly the spines the
  local scheme preserves; a global-Full fallback would destroy them at every
  retry.
- **Cache invalidation landmine**: solving a meta changes the meaning of
  values whose `lazy_eval`s were forced while it was unsolved.
  `Global.register_invalidator` (used by the constant-evaluation cache in
  `norm.ml`) fires on meta mutation, but cached forcings inside *existing
  value refs* are not invalidated by it.  Unification will need a story here:
  generation stamps on solutions, restricting which caches survive a solution
  event, or confining solving to fresh values.
- The pointer-equality shortcut remains sound with metas (physical identity
  still implies definitional equality at any solution state), but beware of
  comparing-then-solving races if equality outcomes are ever cached by pair.

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
