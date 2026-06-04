# Plan: Remove `D.plus_suc`, `D.suc_plus`, `D.suc_plus_eq_suc`

## Goal & non-goals

**Goal:** Remove the three commutativity-dependent functions from `lib/dim/d.ml`, replace all uses with truly general operations from `lib/util/word.ml`. The point is to prepare `lib/dim` for future multi-generator words.

**Non-goals:**
- Actually making `lib/dim` multi-generator (still `Word.Make(Unitcomparable)`).
- Adding singleton assumptions or compare-based runtime bridges (both equivalent to "all generators are equal" and don't actually prepare for multi-generator).

## The fundamental issue

`D.plus_suc`, `D.suc_plus`, `D.suc_plus_eq_suc` perform **rightmost-element shifts** through a plus's middle. The operation has no analog in multi-generator words because `(m, g) suc + n` and `m + (n, g) suc` are literally different types when `n` contains generators other than `g`. `Word.suc_plus` exists but performs a **leftmost shift** — a different operation in multi-generator settings — so it cannot directly substitute.

**Consequence:** algorithms using these functions cannot be rewritten "in place" by substituting word.ml calls. The algorithms themselves must change. Most need their underlying data types to track which generator is consumed at each step, so that when `Word.suc_plus`/`Word.suc_plus_eq_suc` is used, the existential generator in its structured result type-matches the generator carried by the data structure.

## Inventory

### Three D functions

| Function | Signature | Operation |
|---|---|---|
| `D.plus_suc` | `(m suc, n, p) plus -> (m, n suc, p) plus` | Shift unit from left of `m` into right of `n` |
| `D.suc_plus` | `(m, n suc, p) plus -> (m suc, n, p) plus` | Inverse |
| `D.suc_plus_eq_suc` | `(m, n, p) plus -> (m suc, n, p suc) plus` | Add unit to first and third (preserves diff) |

### Call sites (~63 across 7 files)

| File | `plus_suc` | `suc_plus` | `suc_plus_eq_suc` | Total |
|---|---|---|---|---|
| `cube.ml` | 7 | 2 | 0 | 9 |
| `icube.ml` | 4 | 8 | 0 | 12 |
| `tube.ml` | 22 | 0 | 0 | 22 |
| `bwtface.ml` | 0 | 9 | 2 | 11 |
| `pbij.ml` | 2 | 2 | 0 | 4 |
| `shuffle.ml` | 2 | 0 | 1 | 3 |
| `bwsface.ml` | 0 | 2 | 0 | 2 |

(Internal uses in `d.ml` itself: `trichotomy` — already refactored to use `D.factor`.)

### Already done (truly general, no commutativity)

- `lib/dim/sface.ml` `plus_of_sface` — uses `D.factor`
- `lib/dim/tface.ml` `plus_of_tface` — uses `D.factor`
- `lib/dim/d.ml` `trichotomy` — uses `D.factor`
- `lib/util/word.ml` `plus_cast_n` — generic helper added

## Strategy: explicit generators in data types

The recurring pattern: each constructor in our dim data types adds `D.suc` (hardcoded unit). To make algorithms work without `D.plus_suc`/etc., constructors should carry an explicit `'g D.G.t` and parameterize the type as `('n, 'g) D.suc`. Then `Word.suc_plus`'s structured result has its existential `'h` constrainable to that `'g`, removing the need for commutativity-shifts.

### Example transformation

**Before** (`sface.ml`):
```ocaml
type (_, _) sface =
  | Zero : (D.zero, D.zero) sface
  | End : ('m, 'n) sface * 'l Endpoints.t -> ('m, 'n D.suc) sface
  | Mid : ('m, 'n) sface -> ('m D.suc, 'n D.suc) sface
```

**After**:
```ocaml
type (_, _) sface =
  | Zero : (D.zero, D.zero) sface
  | End : ('m, 'n) sface * 'g D.G.t * 'l Endpoints.t -> ('m, ('n, 'g) D.suc) sface
  | Mid : ('m, 'n) sface * 'g D.G.t -> (('m, 'g) D.suc, ('n, 'g) D.suc) sface
```

(For now `'g` only inhabits `unit`, but the type tracks it abstractly.)

This change cascades through every consumer of `sface`. The benefit: when `sface_of_bw_onto` uses `Word.suc_plus`, the resulting `'h` is unified with the `'g` from the matched `End`/`Mid`, and no commutativity step is needed.

### Data types to update

In dependency order (inner → outer):

1. **`sface.ml`** — `sface`, `insert_sface`, `sface_of_plus`, `d_le`
2. **`tface.ml`** — `tface`, `tface_of_plus`, `pface_of_plus`
3. **`bwsface.ml`** — `bwsface`
4. **`bwtface.ml`** — `bwtface`
5. **`shuffle.ml`** — `shuffle`
6. **`cube.ml`** — `gt` (Cube/Branch)
7. **`icube.ml`** — `gt` (IndexedCube/Branch)
8. **`tube.ml`** — `gt` (Tube/Branch)
9. **`pbij.ml`** — `pbij` and friends
10. **`deg.ml`** / **`perm.ml`** — `deg`, `perm` (likely don't need changes; revisit)

## Phasing

### Phase 0 — Setup (this branch)

- ✓ `D.factor`-based rewrites of `plus_of_sface`, `plus_of_tface`, `trichotomy`.
- ✓ `Word.plus_cast_n` helper.
- ✓ Plan document.

### Phase 1 — `sface` first

`sface` is the most-depended-on type. Change its constructors to carry `'g`. Update:

- `sface.ml` itself (~30 functions: `id_sface`, `dom_sface`, `cod_sface`, `comp_sface`, `is_id_sface`, `sface_zero`, `insert_sface`, `sface_plus_sface`, `sface_plus`, `plus_sface`, `sface_of_plus`, `vertex`, `singleton_sface`, `string_of_sface`, `sface_of_string`)
- Update `plus_of_sface` to track generators properly.

**Compile check point:** `dune build lib/dim/sface.ml` and friends (most other dim files will break — that's expected; phase 2 onward fixes them).

### Phase 2 — `tface` and `bwsface`

These directly extend `sface`'s pattern. Similar changes.

`tface_plus`, `plus_tface`, `tface_comp_sface`, `tface_plus_sface`, `sface_plus_tface`, `tface_of_plus`, `pface_of_plus`, `pface_of_sface`, `insert_pface`.

`bwsface`: `dom_bwsface`, `cod_bwsface`, `sface_of_bw`. **This is where `D.suc_plus` is removed for this file** — `sface_of_bw_onto`'s recursion can use `Word.suc_plus` because the `'h` existential aligns with the now-explicit `'g` carried by the matched `End`/`Mid`.

### Phase 3 — `bwtface`

Similar. Removes `D.suc_plus` and `D.suc_plus_eq_suc` here.

### Phase 4 — `shuffle`

`shuffle` already conceptually carries which side adds (Left vs Right). Add `'g` to constructors. `plus_of_shuffle` Left case can use `Word.suc_plus_eq_suc` directly without commutativity, because the `'h` from `Suc_plus_eq_suc`'s result aligns with the `'g` in the matched `Left`. Removes `D.plus_suc` and `D.suc_plus_eq_suc` here.

### Phase 5 — `cube`, `icube`, `tube`

These are larger. `gt`'s `Branch` carries the generator. `gfind`, `gpmapM`, `gbuildM`, etc., all need adjustment. The shared-`m` pattern between `km` and `nm` pluses survives the change: both now carry the same `'g` from the matched `Mid`, and the algorithm uses `Word.suc_plus` whose existential is constrained to that `'g`.

### Phase 6 — `pbij`

Similar to cube/icube.

### Phase 7 — Cleanup

- Remove `D.plus_suc`, `D.suc_plus`, `D.suc_plus_eq_suc` from `d.ml`.
- `dune test` to verify.
- Decide whether `D.suc` keeps its `('n, unit) snoc` alias or becomes obsolete (likely keep for now).

## Concrete first PR (smallest atomic unit)

A reasonable first PR scope:
- Phase 1 (sface) + Phase 2 (tface + bwsface).
- Build passes.
- D's three functions NOT yet removed (still used by cube/icube/tube/etc.).
- Demonstrates the technique end-to-end on the cleanest subgraph.

## Estimated effort

- Phase 1: 1 day (sface is central, many functions touch it).
- Phase 2: 0.5 day (tface) + 0.5 day (bwsface).
- Phase 3: 0.5 day.
- Phase 4: 0.5 day.
- Phase 5: 2 days (largest files).
- Phase 6: 0.5 day.
- Phase 7: 0.5 day.

Total: ~5–6 working days. Best done as a series of incremental PRs with build-green between.

## Open questions for the user

1. **`D.suc` arity:** Keep `'n D.suc = ('n, unit) snoc` (single-param) and have data types use `('n, 'g) Tbwd.snoc` directly? Or generalize `D.suc` to `('n, 'g) D.suc = ('n, 'g) Tbwd.snoc`? The latter is more uniform but cascades wider.

2. **`Unitcomparable.t` constructor visibility at call sites:** Many constructors will need a `Unit` value. Should there be a `D.unit_witness` to centralize, or just pattern-match `Unit` everywhere?

3. **`deg`/`perm`:** Their constructors currently use `Tbwd.insert` rather than `D.suc`, so they may not need changes. Confirm during Phase 1.

4. **Branching point:** Should each phase be its own PR, or all phases on one long-lived branch? The former is reviewable but more friction (some merges will need updating).
