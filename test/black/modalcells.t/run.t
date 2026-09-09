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

The supplied names are sanity-checked.  Mode names may not be reserved words,
and no name may be an invalid identifier.

  $ narya -adjunction -modes 'in,Type' -e 'def foo : Type ≔ Type'
  invalid name: mode name 'in' is a reserved word
  [1]

  $ narya -adjunction -modalities '_x,□' -e 'def foo : Type ≔ Type'
  invalid name: modality name '_x' is not a valid identifier
  [1]

No two modalities, and no two modal cells, may share a name.

  $ narya -adjunction -modalcells 'A,A' -e 'def foo : Type ≔ Type'
  invalid name: duplicate modal cell name 'A'
  [1]

A modal cell may not share a name with a modality, since modalities and cells
are mixed in the parsing of keys.

  $ narya -adjunction -modalcells '△,eps' -e 'def foo : Type ≔ Type'
  invalid name: modal cell name '△' is also a modality name
  [1]

When modalities are single characters, a modal cell name may not be a
concatenation of modality names, which would be ambiguous.

  $ narya -adjunction -modalcells '△□,eps' -e 'def foo : Type ≔ Type'
  invalid name: modal cell name '△□' is a concatenation of modality names, which is ambiguous when modalities are single characters
  [1]
