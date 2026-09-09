{` Lifting on 3-dimensional Π-types.

    This file is deliberately NOT invoked from run.t, so it does not run during
    `dune test`.  It is kept as a reference case, and as a workload for
    profiling higher-dimensional normalization.  Run it by hand with

      dune exec -- narya test/black/hott.t/pi3lift.ny

    The transport fields .trr and .trl at this dimension are cheap and are
    tested in pi3.ny.  The lifting fields are not: each of the two normal forms
    below is about 182500 lines, and computing one costs (as of the commit
    adding this file, on a 16-core 32GB machine) roughly 15 seconds and 4.3GB
    of peak RSS; running this whole file, which does both, takes about 29
    seconds and 6.0GB.  Recording that output in run.t would add some 27MB of
    expected output to the cram test, which is why it lives here instead.

    The axioms come from pi3.ny by `import`, so the two files cannot drift
    apart; importing also replays pi3.ny's own echoes, which is why the first
    few dozen lines of output are its .trr and .trl results.

    For scale, the same computation cost 88 seconds and 25.2GB before the
    optimizations that this file was used to find (lazy normal.ty, the identity
    short-circuit in act_normal, and sharing the identity plus_lock per mode).
    It is a useful canary: it is dominated by promotion and major-heap marking
    rather than by raw allocation, so it exposes retention regressions that the
    smaller tests do not. `}

import "pi3"

echo ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉᵉ⁾ A222 B222
       f022 f122 f202 f212
  .liftr f220 a222

echo ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type)⁽ᵉᵉᵉ⁾ A222 B222
       f022 f122 f202 f212
  .liftl f221 a222
