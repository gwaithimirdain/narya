  $ narya -v -coreflector box.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant □ defined
  
   ￫ info[I0000]
   ￮ constant □map defined
  
   ￫ info[I0000]
   ￮ constant ε defined
  
   ￫ info[I0000]
   ￮ constant △ defined
  
   ￫ info[I0000]
   ￮ constant □ε∘△ defined
  
   ￫ info[I0000]
   ￮ constant ε□∘△ defined
  

  $ narya -coreflector box.ny -e "def g (A : Type) (x : A) : A := f A x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def g (A : Type) (x : A) : A := f A x
     ^ use of id variable behind □ lock requires a key
  
  [1]

  $ narya -coreflector box.ny -e "def η (A :□| Type) (x : A) : □ A := box. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def η (A :□| Type) (x : A) : □ A := box. x
     ^ use of id variable behind □ lock requires a key
  
  [1]

  $ narya -v -functor functor.ny
   ￫ info[I0000]
   ￮ constant ○ defined
  
   ￫ info[I0000]
   ￮ constant ○map defined
  


  $ narya -v -reflector reflector.ny
   ￫ info[I0000]
   ￮ constant diamond defined
  
   ￫ info[I0000]
   ￮ constant diamondmap defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant η defined
  
   ￫ info[I0000]
   ￮ constant ηη defined
  


Unlike the coreflector, the reflector has no counit, so a ◇-locked variable cannot be used directly at its unlocked type.

  $ narya -reflector reflector.ny -e "def ε (A :◇| Type) (x :◇| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def ε (A :◇| Type) (x :◇| A) : A := x
     ^ use of ◇ variable behind id lock requires a key
  
  [1]


  $ narya -v -spatial spatial.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant sharp defined
  
   ￫ info[I0000]
   ￮ constant wsh defined
  
   ￫ info[I0000]
   ￮ constant counit defined
  
   ￫ info[I0000]
   ￮ constant unit defined
  
   ￫ info[I0000]
   ￮ constant wu defined
  


The reflector ♯ has no counit of its own, unlike the coreflector ♭.

  $ narya -spatial spatial.ny -e "def ε (A :♯| Type) (x :♯| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def ε (A :♯| Type) (x :♯| A) : A := x
     ^ use of ♯ variable behind id lock requires a key
  
  [1]


The coreflector ♭ has no unit of its own, unlike the reflector ♯.

  $ narya -spatial spatial.ny -e "def wfl (x : Type) : (data [ flat. (_ :♭| Type) ]) := flat. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def wfl (x : Type) : (data [ flat. (_ :♭| Type) ]) := flat. x
     ^ use of id variable behind ♭ lock requires a key
  
  [1]


The adjunction ♭ ⊣ ♯ only gives cells ♭∘♯ ⇒ id and id ⇒ ♯∘♭, not the other way around.

  $ narya -spatial spatial.ny -e "def nocounit (A :♯ ♭| Type) (x :♯ ♭| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def nocounit (A :♯ ♭| Type) (x :♯ ♭| A) : A := x
     ^ use of ♯ ♭ variable behind id lock requires a key
  
  [1]


  $ narya -spatial spatial.ny -e "def wu2 (x : Type) : (data [ unit2. (_ :♭ ♯| Type) ]) := unit2. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def wu2 (x : Type) : (data [ unit2. (_ :♭ ♯| Type) ]) := unit2. x
     ^ use of id variable behind ♭ ♯ lock requires a key
  
  [1]


Modal fields of records and codata: a field parametrized by the sinister
modality ♭ (with right adjoint ♯) is checked, supplied, and projected behind
the corresponding locks.

  $ narya -v -spatial modalfields.ny
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant C defined
  
   ￫ info[I0000]
   ￮ constant c defined
  
   ￫ info[I0000]
   ￮ constant p defined
  
   ￫ info[I0000]
   ￮ constant p_test defined
  
   ￫ info[I0000]
   ￮ constant proj defined
  
   ￫ info[I0000]
   ￮ constant proj_test defined
  
   ￫ info[I0000]
   ￮ constant R defined
  
   ￫ info[I0000]
   ￮ constant r defined
  
   ￫ info[I0000]
   ￮ constant eta defined
  
   ￫ info[I0000]
   ￮ constant D defined
  
   ￫ info[I0000]
   ￮ constant d defined
  
   ￫ info[I0000]
   ￮ constant d_test defined
  

A modal field projection computes on a comatch/tuple.

  $ narya -spatial modalfields.ny -e "echo p"
  1
    : N
  

A stuck modal projection prints with its locking annotation.

  $ narya -spatial modalfields.ny -e "axiom cc : C" -e "echo (cc :♭| _) .fld"
  (cc :♭| _) .fld
    : N
  

Projecting a modal field with no annotation is an error.

  $ narya -spatial modalfields.ny -e "def bad : N ≔ c .fld"
   ￫ error[E1712]
   ￭ command-line exec string
   1 | def bad : N ≔ c .fld
     ^ field fld is modal with left adjoint ♭, so projecting it requires a locking annotation such as (_ : ♭ | _) .fld
  
  [1]

Projecting a modal field with the wrong locking modality is an error.

  $ narya -spatial modalfields.ny -e "def bad2 : N ≔ (c :♯| _) .fld"
   ￫ error[E1712]
   ￭ command-line exec string
   1 | def bad2 : N ≔ (c :♯| _) .fld
     ^ field fld is modal with left adjoint ♭, but was projected with locking modality ♯
  
  [1]

A field can only be parametrized by a sinister (left adjoint) modality; ♯ is
not sinister.

  $ narya -spatial -e "def Bad : Type ≔ codata [ | (x :♯| _) .f : Type ]"
   ￫ error[E1711]
   ￭ command-line exec string
   1 | def Bad : Type ≔ codata [ | (x :♯| _) .f : Type ]
     ^ modality ♯ is not sinister: it has no declared right adjoint, so it cannot parametrize a modal field
  
  [1]
