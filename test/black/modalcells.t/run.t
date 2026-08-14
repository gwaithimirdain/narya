The -modalcells flag renames the generating 2-cells of the mode theory, so the
unit of the adjunction can be referenced as a key by its new name "myeta".

  $ narya modalcells.ny

The old default name "η" is no longer recognized once the cell has been renamed.

  $ narya oldname.ny
   ￫ error[E1706]
   ￭ $TESTCASE_ROOT/oldname.ny
   7 | def needs_key (A : Disc) (x :□△| A) : □△□△ A ≔ t2. (x #η)
     ^ unknown modal cell η
  
  [1]


Passing the wrong number of modal cell names is an error.

  $ narya -adjunction -modalcells 'onlyone' -e "echo 1"
   ￫ error[E2322]
   ￮ invalid type theory options:
     wrong number of modal cell names for adjunction mode theory
  
  [1]

A locally posetal theory has no nameable cells, so any -modalcells names are rejected.

  $ narya -spatial -modalcells 'x' -e 'def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options:
     wrong number of modal cell names for spatial mode theory
  
  [1]

The supplied names are sanity-checked.  Mode names may not be reserved words,
and no name may be an invalid identifier.

  $ narya -adjunction -modes 'in,Type' -e 'def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options: mode name 'in' is a reserved word
  
  [1]

  $ narya -adjunction -modalities '_x,□' -e 'def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options: modality name '_x' is not a valid identifier
  
  [1]

No two modalities, and no two modal cells, may share a name.

  $ narya -adjunction -modalcells 'A,A' -e 'def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options: duplicate modal cell name 'A'
  
  [1]

A modal cell may not share a name with a modality, since modalities and cells
are mixed in the parsing of keys.

  $ narya -adjunction -modalcells '△,eps' -e 'def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options: modal cell name '△' is also a modality name
  
  [1]

When modalities are single characters, a modal cell name may not be a
concatenation of modality names, which would be ambiguous.

  $ narya -adjunction -modalcells '△□,eps' -e 'def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options:
     modal cell name '△□' is a concatenation of modality names, which is ambiguous when modalities are single characters
  
  [1]
