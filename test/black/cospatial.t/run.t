  $ narya -v -cospatial cospatial.ny
   ￫ info[I0000]
   ￮ constant counit defined
  
   ￫ info[I0000]
   ￮ constant shape defined
  
   ￫ info[I0000]
   ￮ constant wsh defined
  
   ￫ info[I0000]
   ￮ constant ss defined
  
   ￫ info[I0000]
   ￮ constant wss defined
  
   ￫ info[I0000]
   ￮ constant ss2 defined
  
   ￫ info[I0000]
   ￮ constant wss2 defined
  
   ￫ info[I0000]
   ￮ constant ff defined
  
   ￫ info[I0000]
   ￮ constant wff defined
  
   ￫ info[I0000]
   ￮ constant ff2 defined
  
   ￫ info[I0000]
   ￮ constant wff2 defined
  
   ￫ info[I0000]
   ￮ constant sf defined
  
   ￫ info[I0000]
   ￮ constant wsf defined
  
   ￫ info[I0000]
   ￮ constant sf2 defined
  
   ￫ info[I0000]
   ￮ constant wsf2 defined
  
   ￫ info[I0000]
   ￮ constant fs defined
  
   ￫ info[I0000]
   ￮ constant wfs defined
  
   ￫ info[I0000]
   ￮ constant fs2 defined
  
   ￫ info[I0000]
   ￮ constant wfs2 defined
  
   ￫ info[I0000]
   ￮ constant adjunit defined
  
   ￫ info[I0000]
   ￮ constant wau defined
  
   ￫ info[I0000]
   ￮ constant adjcounit defined
  
   ￫ info[I0000]
   ￮ constant Neg defined
  
   ￫ info[I0000]
   ￮ constant mk defined
  
   ￫ info[I0000]
   ￮ constant unmk defined
  
   ￫ info[I0000]
   ￮ constant unmk_mk defined
  
   ￫ info[I0000]
   ￮ constant bad1 defined
  
   ￫ info[I0000]
   ￮ constant bad3 defined
  

A plain value cannot supply a bare ♭-locked field, since ♭ has no unit of its own.

  $ narya -cospatial cospatial.ny -e "def wbad1 (x : Type) : bad1 ≔ bad1. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def wbad1 (x : Type) : bad1 ≔ bad1. x
     ^ use of id variable behind ♭ lock requires a key
  
  [1]

Nor does the reflector ʃ have a counit of its own.

  $ narya -cospatial -e "def bad2 (A :ʃ| Type) (x :ʃ| A) : A ≔ x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad2 (A :ʃ| Type) (x :ʃ| A) : A ≔ x
     ^ use of ʃ variable behind id lock requires a key
  
  [1]

The unit and counit of the induced adjunction ʃ ⊣ ♭ only go in that direction.

  $ narya -cospatial cospatial.ny -e "def wbad3 (x : Type) : bad3 ≔ bad3. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def wbad3 (x : Type) : bad3 ≔ bad3. x
     ^ use of id variable behind ʃ♭ lock requires a key
  
  [1]

  $ narya -cospatial -e "def bad4 (A :♭ʃ| Type) (x :♭ʃ| A) : A ≔ x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad4 (A :♭ʃ| Type) (x :♭ʃ| A) : A ≔ x
     ^ use of ♭ʃ variable behind id lock requires a key
  
  [1]

And there are no 2-cells crossing directly between ʃ and ♭ in the "wrong" direction.

  $ narya -cospatial -e "def bad5 (A :ʃ| Type) (x :♭| A) : A ≔ x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad5 (A :ʃ| Type) (x :♭| A) : A ≔ x
     ^ use of ʃ variable behind ♭ lock requires a key
  
  [1]
