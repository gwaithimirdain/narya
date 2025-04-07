Remarks on implementation
=========================

As is common for normalization-by-evaluation, the implementation uses De Bruijn *indices* for syntactic terms and De Bruijn *levels* for semantic values.  A little more unusually, however, the De Bruijn indices are "intrinsically well-scoped".  This means that the type of terms is parametrized by the length of the context (as a type-level natural number, using GADTs), so that the OCaml compiler ensures *statically* that De Bruijn indices never go out of scope.  Other consistency checks are also ensured statically in a similar way, such as the matching of dimensions for certain types and operators, and scoping and associativity for notations.  (The latter is the reason why tightnesses are dyadic rationals: they are represented internally as type-level finite surreal-number sign-sequences, this being a convenient way to inductively define a dense linear order.)

This approach does have the drawback that it requires a fair amount of arithmetic on the natural numbers to ensure well-typedness, which is not only tedious but some of it also ends up happening at run-time.  Since type-level natural numbers are represented in unary, this could be a source of inefficiency in the future.  However, it has so far proven very effective at avoiding bugs!

Another interesting tool used in the implementation is a technique for writing generic traversal functions for data structures.  With heterogeneous type-indexed lists, we can write a single traversal function that can be called with arbitrarily many data structures as input and arbitrarily many as output, thus including in particular ``map``, ``map2``, ``iter`` (the 0-output case), ``iter2``, and so on.  If this generic traversal is parametrized over a monad, or more generally an applicative functor, then it also includes both left and right folds, possibly combined with maps, and so on.  For a simple data structure like lists this is overkill, of course, but for some of the complicated data structures we use (like n-dimensional cubes that are statically guaranteed to have exactly the right number of elements, accessed by giving a face) it saves a lot of work to be able to implement only one traversal.

The source code is organized in directories as follows:

* `lib/ <https://github.com/gwaithimirdain/narya/tree/master/lib>`_: Most of the code

  * `lib/util/ <https://github.com/gwaithimirdain/narya/tree/master/lib/util>`_: Utilities that could in principle be generic libraries
  
  * `lib/dim/ <https://github.com/gwaithimirdain/narya/tree/master/lib/dim>`_: Definition of the dimension theory (cube category)
  
  * `lib/core/ <https://github.com/gwaithimirdain/narya/tree/master/lib/core>`_: Syntax, normalization, type-checking, etc.
  
  * `lib/parser/ <https://github.com/gwaithimirdain/narya/tree/master/lib/parser>`_: Parsing and printing
  
  * `lib/top/ <https://github.com/gwaithimirdain/narya/tree/master/lib/top>`_: Auxiliary functions for the top-level (executing files, etc.)

* `bin/ <https://github.com/gwaithimirdain/narya/tree/master/bin>`_: The main executable

* `test/ <https://github.com/gwaithimirdain/narya/tree/master/test>`_: Unit tests

  * `test/testutil/ <https://github.com/gwaithimirdain/narya/tree/master/test/testutil>`_: Utilities used only for white-box testing
  
  * `test/white/ <https://github.com/gwaithimirdain/narya/tree/master/test/white>`_: White-box tests of the core
  
  * `test/parser/ <https://github.com/gwaithimirdain/narya/tree/master/test/parser>`_: White-box tests of parsing and printing
  
  * `test/black/ <https://github.com/gwaithimirdain/narya/tree/master/test/black>`_: Black-box tests of the executable
