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

The sharing is preserved in the compiled file, since marshaling preserves it,
and when the compiled file is loaded, since linking updates the origins of
constants in place rather than rebuilding the terms (see Link).  Without
sharing, the compiled file was about 3e7 bytes, and loading it allocated about
8e7 words with a peak heap of 4.6e7 words (and still 5.5e7 and 1.8e7 when the
compiled file was shared but linking rebuilt the terms).  Now the compiled
file is a few kilobytes, and loading it allocates about 6e5 words with a peak
heap of 4e5.

  $ narya -no-reformat synthsharing.ny
  $ wc -c < synthsharing.nyo | awk '{ if ($1 > 100000) print "REGRESSION: compiled file has", $1, "bytes"; else print "compiled file is small" }'
  compiled file is small
  $ echo 'import "synthsharing"' > load.ny
  $ OCAMLRUNPARAM=v=0x400 narya -v -no-reformat load.ny 2>gc.log
  $ grep 'file loaded' gc.log
   ￮ file loaded: $TESTCASE_ROOT/synthsharing.ny (compiled)
  $ awk '/allocated_words:/ { a = $2 } /top_heap_words:/ { h = $2 } END {
  >   if (a + 0 > 5000000 || h + 0 > 5000000) printf "REGRESSION: loading allocated %d words with peak heap %d\n", a, h
  >   else print "loading within budget"
  > }' gc.log
  loading within budget
