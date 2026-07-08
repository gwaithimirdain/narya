The Dtt mode theory (adjoint triple ◇ ⊣ △ ⊣ □ over two modes Disc and Type).

  $ narya -dtt -v dttmodal.ny
   ￫ info[I0000]
   ￮ constant C defined
  
   ￫ info[I0001]
   ￮ axiom z assumed
  
   ￫ info[I0000]
   ￮ constant K defined
  
   ￫ info[I0001]
   ￮ axiom k assumed
  
   ￫ info[I0000]
   ￮ constant counit defined
  

Modal field projections land in the adjoint modality's target mode.

  $ narya -dtt dttmodal.ny -e "echo (z :◇| _) .fld"
  (z :◇| _) .fld
    : Disc
  

  $ narya -dtt dttmodal.ny -e "echo (k :△| _) .obj"
  (k :△| _) .obj
    : Type
  

A modal field must be parametrized by a sinister modality.  △ and ◇ are sinister
(left adjoints); □ is not.

  $ narya -dtt -e "def Bad : Type ≔ codata [ (x :□| _) .f : Disc ]"
   ￫ error[E1711]
   ￭ command-line exec string
   1 | def Bad : Type ≔ codata [ (x :□| _) .f : Disc ]
     ^ modality □ is not sinister: it has no declared right adjoint, so it cannot parametrize a modal field
  
  [1]

find_unique: a variable annotated by the coreflector △□ can be used unlocked
(the counit △□ ⇒ id provides the key), but a bare △ cannot (there is no △ ⇒ id).

  $ narya -dtt -v -e "def ok (A :△ □| Type) : Type := A"
   ￫ info[I0000]
   ￮ constant ok defined
  

  $ narya -dtt -e "def bad (A :△| Disc) : Type := A"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad (A :△| Disc) : Type := A
     ^ use of △ variable behind id lock requires a key
  
  [1]
