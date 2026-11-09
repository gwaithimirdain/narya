Performance regression guard for sharing in readback (issue #145).

The synthesized type of h is the type of g with F substituted by a function
that uses its argument three times, so as a tree it has size 3^12, although
as a value it shares its subterms.  The type of a definition without a type
annotation is read back to be stored, and without sharing in readback (see
Readback.sharing) that readback, and the term it produces, are as large as the
tree: about 6.9e8 words allocated and 2.4e7 words peak heap.  With sharing they
are about 1.1e6 and 4.5e5.  As in veryslow.t, we assert on OCaml's allocation
and peak heap rather than on time, with budgets that leave wide headroom over
the current figures but catch a return of the blowup.

  $ OCAMLRUNPARAM=v=0x400 narya -no-reformat -source-only synthsharing.ny 2>gc.log
  $ awk '/allocated_words:/ { a = $2 } /top_heap_words:/ { h = $2 } END {
  >   alloc_budget = 50000000
  >   heap_budget  = 5000000
  >   ok = 1
  >   if (a + 0 > alloc_budget) {
  >     printf "REGRESSION: allocated %d words > budget %d\n", a, alloc_budget
  >     ok = 0
  >   }
  >   if (h + 0 > heap_budget) {
  >     printf "REGRESSION: peak heap %d words > budget %d\n", h, heap_budget
  >     ok = 0
  >   }
  >   if (ok) print "allocation and peak heap within budget"
  > }' gc.log
  allocation and peak heap within budget
