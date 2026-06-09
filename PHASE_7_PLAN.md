# Phase 7 Plan: Remove `D.plus_suc` / `D.suc_plus` / `D.suc_plus_eq_suc`

## Current state (as of 2026-06-09)

After session 2 work: `shuffle.ml` fully restructured.  `gfind` family restructured in cube/icube/tube (drops the redundant `km`/`mq` plus argument since gt+sface types already encode the dimensional alignment).

| File | `D.plus_suc` / `D.suc_plus_eq_suc` | `D.suc_plus` | Status | Remaining algorithm shape |
|---|---|---|---|---|
| `shuffle.ml` | 0 | 0 | **done** | — |
| `cube.ml` | 5 | 2 | gfind done | gpmapM, gbuildM, CubeOf.lift/lower |
| `icube.ml` | 3 | 8 | gfind done | gmapM, gset, gfold_map_left/right, gbuild_left |
| `tube.ml` | 21 | 0 | gfind done | gpmapM_l/_ll/_r, gbuildM_l/_ll/_r, glift, glower |
| `pbij.ml` | 4 | 3 | TODO | gfind, gset, gbuild, gpmapM |
| `bwsface.ml` | 0 | 3 | TODO | sface_of_bw_onto (accumulator) |
| `bwtface.ml` | 2 | 11 | TODO | tface_of_bw_r, tface_of_bw_lt, tface_of_bw_ls |

**Tried in session 2 and reverted**: naive recursive `sface_of_bw`, `sface_plus_sface`-based `sface_of_bw`, dropping `mq` from `tube.gfind` with weaker constraints — all break either type-checking or hott bootstrap.  The hott break confirms the orientation flip is load-bearing semantically, not just a quirk of the original implementation.

## What "removing" actually means

The three D functions perform **rightmost-element shifts** on a plus's middle (e.g., `(m suc, n, p) plus → (m, n suc, p) plus`).  This operation has no analog in multi-generator words because `(m, g) suc + n` and `m + (n, g) suc` are different types when `n` contains generators other than `g`.

So "remove them" actually means "restructure the algorithms so they don't need to perform that shift."  Three patterns to recognize:

1. **Shift-then-destruct:** `let (Suc (km', Unit)) = D.plus_suc km in ...`
   - Used as a unit-only peeling of `(k_suc, m, km) plus` to `(k, m, km_inner) plus + km = km_inner suc`.
   - In multi-generator: requires commutativity to define.  Must be replaced by an algorithm that doesn't ask for this rotation.

2. **Pure shift:** `D.suc_plus ln` passed forward to recursion.
   - Used to "consume" a generator step on the middle by adding it to the left.
   - Multi-generator-friendly form requires the caller to provide the generator explicitly and/or restructure to track it.

3. **Add-to-both:** `D.suc_plus_eq_suc p` where `p : (m, n, p) plus`.
   - Used to produce `(m suc, n, p suc) plus` — added the same g on both sides.
   - Multi-generator-friendly: the caller knows the g (from the matched constructor) and the result type aligns.

## Phasing — easiest to hardest

### 7a — `shuffle.ml` (4 calls, smallest)

`plus_of_shuffle`, `deg_of_shuffle`, `perm_of_shuffle` — all Left case calls `D.suc_plus_eq_suc` / `D.plus_suc` on a recursive plus.

This is the cleanest test bed for **pattern (3)**: the Left constructor now carries an explicit `'g`, so the (m suc, n, p suc) plus we want to produce is exactly `(m, g) suc + n = (p, g) suc`.  Word's structured `suc_plus_eq_suc` produces exactly this when the matched g is threaded in.

**Estimated cost:** 30 min.  **Risk:** low — small file, no dependencies.

### 7b — `cube.ml` (9 calls)

The canonical example.  Establishes the pattern that `icube`, `tube`, `pbij` will follow.

Key functions:
- `gfind` Mid case (pattern 1)
- `gpmapM` Branch case (pattern 2, paired km/lm shifts)
- `gbuildM` Branch case (pattern 2, three plus shifts)
- `CubeOf.lift`/`lower` (pattern 1)

Likely approach: change the `km`/`lm` plus arguments so that the algorithm carries `(k, m, km_inner) plus` directly rather than `(k_suc, m, km) plus`.  In multi-generator-aware code, this means the recursion descends into Branch's inner `br : (m, (n_inner, g) suc, b) gt` with km already restricted to the inner dimension.

**Estimated cost:** 2–3 hours.  **Risk:** medium — sets the template for downstream files.

### 7c — `icube.ml` (12 calls)

Same shape as cube.ml but more functions (gmapM, gset, gfold_map_left, gfold_map_right, gbuild_left).  Should be mostly mechanical once 7b is done.

**Estimated cost:** 1–2 hours.  **Risk:** low if 7b is solid.

### 7d — `tube.ml` (22 calls)

Largest count, but tube's gt is structurally similar to cube/icube.  The functions split into `_l`/`_ll`/`_r` variants (left-uninstantiated, left-left, right) but each variant follows the same pattern as the cube version.

**Estimated cost:** 2–3 hours.  **Risk:** low if 7b is solid (mostly cut-and-paste with adjustments).

### 7e — `pbij.ml` (7 calls)

`gfind`, `gset`, `gbuild`, `gpmapM` all use the Suc-of-`Pbijmap.gt` with `D.plus_suc r12`.  The pattern is the same — restructure to keep `r12` aligned with the recursive structure.

**Estimated cost:** 1–2 hours.  **Risk:** low.

### 7f — `bwsface.ml` (3 calls) + `bwtface.ml` (13 calls)

The accumulator algorithms (`sface_of_bw_onto`, `tface_of_bw_r/_lt/_ls`).  These reverse the order (outer bwsface End → inner sface End — see Phase 2 commit), which is the part that fights an obvious commutativity-free rewrite.

Likely approach: process bwsface/bwtface inner-to-outer instead of outer-to-inner.  Use `sface_plus_sface` / `tface_plus` / `sface_plus_tface` from sface.ml/tface.ml as the composition primitive (already commutativity-free).  Need to verify orientation matches the existing semantics — the hott bootstrap is the canary.

**Estimated cost:** 2–3 hours.  **Risk:** highest — Phase 2 already showed the naive rewrite reverses the orientation.

### 7g — final cleanup

- Remove `plus_suc` / `suc_plus_eq_suc` / `suc_plus` from `lib/dim/d.ml`.
- Build + `dune test` + commit.
- Sweep for any remaining stub `TODO` comments referencing G.compare bridges that should now be gone.

**Estimated cost:** 30 min.

## Total estimate

~10–14 hours of focused work, spread across 7 commits.

## Verification at each step

- `dune build` after every change.
- `dune test` (or at least `dune build @runtest` for the hott bootstrap) at end of each 7a–7f.
- Look at the `git diff` to confirm only the intended `G.compare g D.deg` bridges were removed.

## Open question

If in 7b–7e the restructuring requires changing function signatures (e.g., gfind no longer takes a plus arg, or takes a different plus structure), the callers also have to change.  If the signature changes are large enough to be invasive, an alternative is to keep the simple plus signature externally but use a Word-structured form internally with G.compare validating that the bridges hold.  That second approach is "honest single-direction" rather than "preparation for multi-generator" and effectively reverts to the previous bridge style.  Decision needed: if a Phase 7 file's restructuring turns out to require breaking the signature, do we (a) take the breakage, or (b) keep the signature with internal G.compare?
