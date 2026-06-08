# Phase 7 Findings: What "Genuine Restructuring" Actually Requires

After committing to genuine restructuring (no `Word.compare` / `G.compare` bridges), I tried Phase 7a on `shuffle.ml` and Phase 7b on `cube.ml` and hit walls fast.  Each remaining file's commutativity dependence is structurally different, and "remove the D function" turns out to mean very different things per file.

## What the three D functions actually do

| Function | Operation | Multi-generator analog in word.ml? |
|---|---|---|
| `D.plus_suc` | shift unit from m's right to n's left in `(m_suc, n, p) plus` | `Word.plus_suc` (structured) — but it returns the LEFTMOST shift, not rightmost.  Same in single-direction, different in multi-direction. |
| `D.suc_plus` | inverse of `plus_suc` | `Word.suc_plus` — same caveat. |
| `D.suc_plus_eq_suc` | add unit to both first and third of `(m, n, p) plus` | `Word.suc_plus_eq_suc` — returns plus + insertion, the insertion is at the leftmost position, not rightmost. |

D's three functions perform **rightmost-element shifts**.  Word.ml has no rightmost-shift operation, because rightmost-shift is exactly the commutativity-dependent operation that has no multi-generator definition.

## Per-file scope of "genuine restructuring"

### `shuffle.ml`
The shuffle data type itself encodes commutativity:

```ocaml
Left : ('a, 'b, 'ab) shuffle * 'g G.t -> (('a, 'g) suc, 'b, ('ab, 'g) suc) shuffle
```

This says: a shuffle of (a + g) with b interleaves to (ab + g).  At the value level, ab = a + b, so the result type assumes `(a + g) + b = (a + b) + g` — that's commutativity.

To genuinely restructure: redesign the `shuffle` data type so the Left constructor's third type argument is computed by **inserting** g into the recursive shuffle's output (e.g., `('ab, 'g, 'ab_g) Tbwd.insert`).  Cascade through `plus_of_shuffle`, `deg_of_shuffle`, `perm_of_shuffle`, `comp_shuffle_right`, `all_shuffles_right`, and every caller of these in `pbij.ml`, `core/`.

**Estimated scope:** the data type change alone is a day; the cascade across ~6 functions and ~10 call sites is another day.  ~2 days total for just shuffle.

### `cube.ml`
`gfind` Mid case shifts the gt's height-generator off the LHS of km's plus.  The shift is needed because `gt`'s outer dim is `(m_pre, g) suc` and the Branch's `br` is `(m_pre, …)`.  Walking gt down by one step takes a `(k_outer, m, km) plus` to a `(k_inner, m, m_pre) plus`, which is exactly the rightmost shift.

Genuine restructuring would mean changing gfind's signature so it doesn't accumulate `(k, m, km) plus` at all — perhaps walking only the sface and gt and recovering plus relationships at the leaf via `factor`/`compare`.  Same restructuring would need to apply to `gpmapM`, `gbuildM`, `CubeOf.lift`, `CubeOf.lower`, and every cube-Heter traversal.

**Estimated scope:** the gfind redesign is 1–2 days alone; gpmapM and gbuildM each similar; CubeOf.lift/lower another day.  ~4–5 days for cube.

### `icube.ml`
Same shape as cube but with more functions and the extra `branches` GADT.  ~5 days.

### `tube.ml`
Largest; 22 calls across `_l`/`_ll`/`_r` variants of gpmapM/gbuildM plus glift/glower/gfind.  ~6–7 days.

### `pbij.ml`
The Pbijmap traversal mirrors cube's pattern.  ~2 days.

### `bwsface.ml`
The accumulator algorithm in `sface_of_bw_onto` walks bwsface outer-to-inner while building the sface, using `D.suc_plus` to shift the `ln` plus's middle to its left at each step.  Phase 2 showed that the obvious commutativity-free rewrite using `sface_plus_sface` **reverses the orientation** (bwsface outer-End → sface outer-End instead of inner-End), which breaks the hott bootstrap.

Genuine restructuring needs a different algorithm that preserves the existing semantics without rightmost shifts.  Possibilities: explicitly reverse the bwsface first, then walk it forward.  Or carry an additional structure (e.g., a list of pending generator additions) that gets composed via `sface_plus_sface` only at the end.

**Estimated scope:** 1–2 days (algorithm redesign + verification).

### `bwtface.ml`
Same family as bwsface, three helper functions instead of one, each with the same accumulator structure.  ~2–3 days.

## Cumulative honest estimate

~20–25 days of focused work for genuine restructuring of all six algorithm-heavy files, plus the final removal of D's three functions from d.ml.

## Recommendation

This is a real project, not a session.  Two practical paths from here:

1. **Pick one algorithm and do it properly** — e.g., shuffle (smallest data-type cascade) — then evaluate whether the result is good enough to template the rest.
2. **Land Phases 0–6 as preparation, defer Phase 7** — the current state has every data type generator-ready and every algorithm bridged with `G.compare g D.deg`.  In a future multi-generator world, the bridges would fail loudly at the call sites that need redesign, marking the work to do.  The branch is shippable as honest preparation.

Either way, Phase 7 needs more time than a single session.

## Session 2 progress and learnings (2026-06-08)

### Completed
- `shuffle.ml`'s `deg_of_shuffle`/`perm_of_shuffle` restructured around `strip_left_g` and `*_with_extra` (no D bridges).  `plus_of_shuffle` dropped.
- `cube.ml`'s `gfind` dropped its `km` plus argument: the sface and gt types together already encode the dimensional alignment, and `tube.ml`'s caller is updated.

### Confirmed blockers (algorithm redesign needed, not just rewrites)

**`bwsface.ml` `sface_of_bw`**: Naive recursive rewrite type-checks but breaks the hott bootstrap because it flips orientation.  Original semantics: bwsface's outer-End → sface's inner-End.  The bwsface's codom word is the **reverse** of the cube's codom word.  Genuine multi-direction fix requires either (a) a type-level reverse on the codom word, or (b) a different bwsface data design where outer-constructor IS outer-End semantically.  Neither is local.

**`tube.ml`/`icube.ml` `gfind`/`gpmapM`/`gbuildM`**: Carry two plus relations `(m, q, nk)` and `(p, q, pq)` whose `q` is shared.  In the Mid recursion, m and nk both shrink by g while q must absorb the g via `D.plus_suc` (rightmost shift) so that the recursive call sees a consistent q.  In multi-direction, q's g may differ from m/nk's g — there is no commutativity-free way to maintain a single shared q across the shift.  Word.ml's structured `plus_suc`/`suc_plus` give the right relations but with existential q', and the existential doesn't match the recursion's required type.  Fix requires changing the gfind family's type signatures to thread per-step plus relations differently (likely insertion-based throughout), which cascades into every cube/tube/icube algorithm.

**`CubeOf.lift`/`lower`**: Fundamentally commutativity-dependent in type.  The outer generator after lift would be either the input's outer-g or n2's rightmost — the algorithm assumes the former.  In multi-direction, lift/lower as currently typed simply cannot exist; they'd need either restriction to interior dims or a permutation witness.

**`pbij.ml` `gfind`/`gset`/`gpmapM`**: Same shape as cube/tube — `r12 : (r1, r2, r) plus` shifts a g via `D.suc_plus` in the Left case.  Same blocker.

### Where the work actually lives

The unifying redesign is: replace `(a, b, ab) D.plus` tracking in algorithm recursions with `(a, g, ab) D.insert` (insertion) chains.  Insertions naturally describe "where the generator went" without requiring commutativity.  This means redesigning at minimum:
- cube.ml's `gpmapM`/`gbuildM`/`lift`/`lower` (and their `gt` data dependencies if applicable)
- tube.ml's `gpmapM_l`/`_ll`/`_r` and `gbuild*` (~10 callsites)
- icube.ml's `gmapM`/`gfold_*`/`gbuild_*` (parallel to cube/tube)
- pbij.ml's `gfind`/`gset`/`gpmapM`
- bwsface.ml — possibly by redesigning bwsface itself to carry an insertion witness for its outer position

This is the ~20-25 day estimate.  Without this, every replacement of `D.plus_suc`/`D.suc_plus`/`D.suc_plus_eq_suc` with a Word-ml structured equivalent triggers a cascade of existential q's that don't match the surrounding algorithm's type signature.
