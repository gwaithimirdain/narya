The -modalcells flag renames the generating 2-cells of the mode theory, so the
unit of the adjunction can be referenced as a key by its new name "myeta".

  $ narya -adjunction -modalcells 'myeta,myeps' modalcells.ny

The old default name "η" is no longer recognized once the cell has been renamed.

  $ narya -adjunction -modalcells 'myeta,myeps' oldname.ny
   ￫ error[E1706]
   ￭ $TESTCASE_ROOT/oldname.ny
   5 | def needs_key (A : Disc) (x :□△| A) : □△□△ A ≔ t2. (x #η)
     ^ unknown modal cell η
  
  [1]


Passing the wrong number of modal cell names is an error.

  $ narya -adjunction -modalcells 'onlyone' modalcells.ny
  Fatal error: exception Failure("wrong number of modal cell names for adjunction mode theory")
  [2]

A locally posetal theory has no nameable cells, so any -modalcells names are rejected.

  $ narya -spatial -modalcells 'x' -e 'def foo : Type ≔ Type'
  Fatal error: exception Failure("wrong number of modal cell names for spatial mode theory")
  [2]
