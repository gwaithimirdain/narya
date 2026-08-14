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

  $ narya -e "option modal ≔ adjunction, modalcells onlyone echo 1"
   ￫ error[E2322]
   ￮ invalid type theory options:
     wrong number of modal cell names for adjunction mode theory
  
  [1]

A locally posetal theory has no nameable cells, so any -modalcells names are rejected.

  $ narya -e 'option modal ≔ spatial, modalcells x def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options:
     wrong number of modal cell names for spatial mode theory
  
  [1]

The supplied names are sanity-checked.  Mode names may not be reserved words,
and no name may be an invalid identifier.

  $ narya -e 'option modal ≔ adjunction, modes in Type def foo : Type ≔ Type'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | option modal ≔ adjunction, modes in Type def foo : Type ≔ Type
     ^ parse error: invalid syntax
  
  [1]

  $ narya -e 'option modal ≔ adjunction, modalities _x □ def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options: modality name '_x' is not a valid identifier
  
  [1]

No two modalities, and no two modal cells, may share a name.

  $ narya -e 'option modal ≔ adjunction, modalcells A A def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options: duplicate modal cell name 'A'
  
  [1]

A modal cell may not share a name with a modality, since modalities and cells
are mixed in the parsing of keys.

  $ narya -e 'option modal ≔ adjunction, modalcells △ eps def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options: modal cell name '△' is also a modality name
  
  [1]

When modalities are single characters, a modal cell name may not be a
concatenation of modality names, which would be ambiguous.

  $ narya -e 'option modal ≔ adjunction, modalcells △□ eps def foo : Type ≔ Type'
   ￫ error[E2322]
   ￮ invalid type theory options:
     modal cell name '△□' is a concatenation of modality names, which is ambiguous when modalities are single characters
  
  [1]
