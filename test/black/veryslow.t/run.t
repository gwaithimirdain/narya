Performance regression guard.

veryslow.ny builds univalence from quasi-invertible maps via `glue` and ends
with `retract_Id_Equiv`, whose final `is_contr` conversion under a
1-dimensional binder repeatedly triggered super-linear blowups during
development of glued evaluation and the equality checker (see
lib/core/EQUAL.md for the history).

Rather than a wall-clock timeout, which varies by machine, we assert on
OCaml's total allocation and peak heap.  Both are deterministic and
machine-independent for a given binary (allocation exactly so; peak heap up to
GC-tuning), which a timeout is not.  Allocation churn catches recomputation
blowups (the glued-mode pathology, which reached tens of billions of words);
peak heap catches retention blowups (the eager-mode pathology, which reached
tens of gigabytes).  The budgets have wide headroom over current figures and
exist to catch a *return* of those blowups, not to police small changes.

Current figures (these may drift with the evaluator and the compiler):
glued evaluation on is about 1.4e8 words allocated and 3e6 words peak heap;
glued evaluation off is about 1.6e9 words allocated and 4e7 words peak heap.

The budgets below (5e9 / 5e8) pass in either state of the glued-evaluation
toggle in value.ml, so flipping it does not spuriously fail this test.  If a
genuine algorithmic change moves the figures near a budget, re-baseline it.

  $ OCAMLRUNPARAM=v=0x400 narya -no-reformat -source-only veryslow.ny 2>gc.log
  $ awk '/allocated_words:/ { a = $2 } /top_heap_words:/ { h = $2 } END {
  >   alloc_budget = 5000000000
  >   heap_budget  = 500000000
  >   ok = 1
  >   if (a + 0 > alloc_budget) {
  >     printf "REGRESSION: allocated %d words > budget %d (see lib/core/EQUAL.md)\n", a, alloc_budget
  >     ok = 0
  >   }
  >   if (h + 0 > heap_budget) {
  >     printf "REGRESSION: peak heap %d words > budget %d (see lib/core/EQUAL.md)\n", h, heap_budget
  >     ok = 0
  >   }
  >   if (ok) print "allocation and peak heap within budget"
  > }' gc.log
  allocation and peak heap within budget
