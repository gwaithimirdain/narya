# Profiling Narya

Notes on how to measure Narya's time and memory, which workloads are worth
measuring, and what the numbers looked like as of July 2026.  Nothing here is
required to build or use Narya; it is for people investigating performance.

The short version: **higher-dimensional normalization is dominated by promotion
and major-heap marking, not by raw allocation.**  Ranking allocation sites will
send you to the wrong place.  Measure what *survives*.

## Workloads

| File | What it exercises | Cost |
| --- | --- | --- |
| `test/black/hott.t/pi2.ny` | 2-dimensional Π, all four operations | ~3.1s, ~115MB |
| `test/black/hott.t/pi3.ny` | 3-dimensional Π, `.trr`/`.trl` only | ~0.5s, ~38MB |
| `test/black/hott.t/sigma3.ny` | 3-dimensional Σ, all four operations | ~2.5s, ~134MB |
| `test/black/hott.t/pi3lift.ny` | 3-dimensional Π, `.liftr` and `.liftl` | ~29s, ~6.0GB |
| `test/black/veryslow.t/veryslow.ny` | univalence via `glue`; asserts on allocation and peak heap | see its `run.t` |

`pi3lift.ny` is deliberately **not** invoked from `run.t`, so it does not run
during `dune test`; run it by hand.  It is the most useful stress case: each of
its two normal forms is about 182500 lines, and it is dominated by retention
rather than by allocation, so it exposes regressions the smaller tests do not.

Note the contrast between `pi3lift.ny` and `sigma3.ny`.  Transport and lifting
in a Σ-type decompose into the corresponding operations on the two components,
so the normal forms stay small; in a Π-type they do not.  All four Σ operations
at dimension 3 cost about a thirtieth of the memory of a single Π lift.

Narya rewrites `.ny` files given on the command line and writes `.nyo` and
`.bak` files beside them, so profile **copies**, or pass `-no-reformat`.

## GC counters: the cheapest useful measurement

```
OCAMLRUNPARAM=v=0x400 /usr/bin/time -v narya -no-reformat pi3lift.ny
```

This prints `allocated_words`, `promoted_words`, `top_heap_words` and the
collection counts at exit.  `allocated_words` is **exactly deterministic** for a
given binary and input, which makes it a far better regression signal than wall
time; `top_heap_words` is deterministic up to GC tuning.  This is the technique
`test/black/veryslow.t` uses to assert on performance without a timeout.

The ratio `promoted_words / allocated_words` is the number to watch.  Anything
much above ~5% means short-lived data is surviving the minor heap, and the major
GC will dominate.

## perf

Needs two kernel settings, which most distributions lock down:

```
sudo sysctl -w kernel.perf_event_paranoid=1 kernel.yama.ptrace_scope=0
```

`perf_event_paranoid=1` allows user+kernel profiling of your own processes
(`-1` for system-wide).  `ptrace_scope=0` allows attaching to an already-running
process; at the default `1` you may only attach to descendants, so `gdb -batch
--args ...` works but sampling a running `narya` does not.

The opam switch matters.  A default switch has no frame pointers, and perf then
**cannot unwind through `caml_call_gc` into OCaml frames** — which is exactly
where the interesting stacks are, since most samples are reached from an
allocation poll point.  Build a switch with frame pointers:

```
opam switch create narya-fp ocaml-variants.5.3.0+options ocaml-option-fp
eval $(opam env --switch=narya-fp)
opam install --deps-only --with-test .
dune build
```

Then

```
perf record -F 499 --call-graph=fp -o perf.data -- narya -no-reformat pi3lift.ny
perf report -i perf.data --stdio --no-children -g none --percent-limit 1
```

`--call-graph=fp` produces roughly a third the data of `--call-graph=dwarf` and
unwinds correctly.  Verify the fp switch reproduces the same `allocated_words`
as your normal switch before trusting its profile.

Two gotchas:

* The tree views (`perf report -g caller`) tend to collapse, because eval
  recursion makes stacks deeper than perf's frame limit.  Aggregate `perf
  script` output yourself instead.
* To attribute allocation, take the samples that pass through `caml_call_gc` and
  tally the innermost frame above it that is not a runtime symbol
  (`caml_*`, `do_some_marking`, `oldify_*`, `pool_*`, ...).

## Retention: `Gc.Memprof`

perf tells you what allocates.  It does not tell you what *survives*, and on
these workloads those are different questions — the biggest allocation site can
be memory that dies young, while a site allocating a few words per call can
dominate the live heap because the results are all retained.

`Gc.Memprof`'s `promote` callback fires exactly when a sampled minor-heap block
survives into the major heap, so tallying allocation backtraces at promotion
gives a retention profile.  Sanity-check any such profile by comparing its
promoted/allocated sample ratio against the `OCAMLRUNPARAM=v=0x400` counters;
they should agree closely.

Add this to `bin/narya.ml` temporarily (it is not part of the shipped binary),
then run with `NARYA_MEMPROF=1e-5`:

```ocaml
let () =
  match Sys.getenv_opt "NARYA_MEMPROF" with
  | None -> ()
  | Some r ->
      let rate = try float_of_string r with _ -> 1e-4 in
      let tbl : (string, int) Hashtbl.t = Hashtbl.create 4096 in
      let promoted = ref 0 and allocated = ref 0 in
      let key (a : Gc.Memprof.allocation) =
        let s = Printexc.raw_backtrace_to_string a.callstack in
        String.concat "|" (List.filteri (fun i _ -> i < 6) (String.split_on_char '\n' s)) in
      let add k n =
        Hashtbl.replace tbl k (n + Option.value ~default:0 (Hashtbl.find_opt tbl k)) in
      let tracker : (_, _) Gc.Memprof.tracker = {
        alloc_minor = (fun a -> allocated := !allocated + a.n_samples; Some (key a, a.n_samples));
        alloc_major = (fun a ->
          allocated := !allocated + a.n_samples;
          promoted := !promoted + a.n_samples;
          add (key a) a.n_samples; None);
        promote = (fun (k, n) -> promoted := !promoted + n; add k n; None);
        dealloc_minor = (fun _ -> ());
        dealloc_major = (fun _ -> ());
      } in
      ignore (Gc.Memprof.start ~sampling_rate:rate ~callstack_size:24 tracker);
      at_exit (fun () ->
          Gc.Memprof.stop ();
          let l = Hashtbl.fold (fun k v acc -> (v, k) :: acc) tbl [] in
          let l = List.sort (fun (a, _) (b, _) -> compare b a) l in
          Printf.eprintf "\n=== retention: %d promoted / %d allocated samples ===\n"
            !promoted !allocated;
          List.iteri (fun i (v, k) ->
              if i < 25 then
                Printf.eprintf "%6.2f%%  %s\n"
                  (100. *. float_of_int v /. float_of_int (max 1 !promoted))
                  (String.concat "\n         " (String.split_on_char '|' k))) l)
```

memtrace's command-line tools crash decoding traces from this program (an assert
in `location_codec`), so use `Gc.Memprof` directly as above.

## Where the time goes in an `echo`

To split a command into phases, instrument the `Echo` branch of
`lib/parser/command.ml`, which runs `Check.synth`, then `Norm.eval_term`, then
`readback_at`, then `unparse`, then `PPrint`.  Printing `Unix.gettimeofday` and
`Gc.quick_stat` between those stages showed, for one dimension-3 Π lift before
the July 2026 optimizations:

```
synth 0.06s | eval 67.07s (heap 20.2GB) | readback 18.81s (heap 24.3GB)
            | unparse 1.17s | print 0.27s
```

That is, evaluation dominates and printing is noise.  Beware of concluding
otherwise from `def x ≔ <expr>`, which looks nearly free because it stores the
value lazily and never forces it; it is not a proxy for the cost of normalizing.

## Results as of July 2026

On `pi3lift.ny`'s `.liftr`, three changes took it from 88.3s/25.2GB to
15.0s/4.28GB — 5.9x faster in 5.9x less memory, with byte-identical output:

* **Lazy `normal.ty`** (`lib/core/value.ml`).  A normal carries a value with its
  type, but the type is often never used.  Computing it eagerly was expensive
  because `tyof_lower_codatafield` builds an instantiation tube whose entries
  each recursively call `tyof_field`, which is exponential in dimension.
  84.3s -> 42.0s, 25.2GB -> 12.3GB.
* **Identity short-circuit in `act_normal`** (`lib/core/act.ml`).  The public
  `act_*` entry points are wrapped in `short_circuit`, but the recursive calls
  inside `module Act` are not, and `act_apps` factors the degeneracy per face, so
  an identity residual arrives deep in the recursion with nothing to test it —
  96.2% of internal `act_normal` calls.  42.0s -> 16.3s, 12.3GB -> 5.0GB.
* **Sharing the identity `plus_lock` per mode** (`lib/core/tctx.ml`).  Its
  content depends only on the mode, and it is stored into locked contexts that
  survive.  Total allocation barely moves (-0.4%) but promoted words fall 13.4%.
  16.3s -> 15.0s, 5.0GB -> 4.28GB.

Two things that did *not* work, both of which looked promising by allocation:

* Removing `Monad.Maybe`'s closures from `Word.factor`, the single largest
  allocation site at 22.7%, cut total allocation 27.7% but bought only 4.5% of
  time and no memory at all: those closures died in the minor heap.
* Caching `Insertion.id_ins` cut peak RSS 6.7% but cost 2.8% of time and
  *increased* allocation, because building the cache key calls `D.plus_right`,
  which allocates.  A cache whose key construction allocates can lose to what it
  saves when the cached value is small.

The general lesson, stated once more: allocation rank and retention rank are
different, and on these workloads retention is what predicts the win.
