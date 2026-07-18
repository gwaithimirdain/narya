  $ narya -v -coreflector box.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant ♭ defined
  
   ￫ info[I0000]
   ￮ constant ♭map defined
  
   ￫ info[I0000]
   ￮ constant ε defined
  
   ￫ info[I0000]
   ￮ constant △ defined
  
   ￫ info[I0000]
   ￮ constant ♭ε∘△ defined
  
   ￫ info[I0000]
   ￮ constant ε♭∘△ defined
  

  $ narya -coreflector box.ny -e "def g (A : Type) (x : A) : A := f A x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def g (A : Type) (x : A) : A := f A x
     ^ use of id variable behind ♭ lock requires a key
  
  [1]

  $ narya -coreflector box.ny -e "def η (A :♭| Type) (x : A) : ♭ A := box. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def η (A :♭| Type) (x : A) : ♭ A := box. x
     ^ use of id variable behind ♭ lock requires a key
  
  [1]

  $ narya -v -functor functor.ny
   ￫ info[I0000]
   ￮ constant ○ defined
  
   ￫ info[I0000]
   ￮ constant ○map defined
  
   ￫ info[I0000]
   ￮ constant Id○ defined
  
   ￫ info[I0000]
   ￮ constant refl_circ defined
  
   ￫ info[I0000]
   ￮ constant to_Id defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/functor.ny
   28 |            match u0, u1 [ circle. x0, circle. x1 ↦ ○ (Id A x0 x1) ] [
      ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant from_Id defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/functor.ny
   37 |            match u0, u1 [
   38 |            | circle. x0, circle. x1 ↦
   39 |                Id (Id (○ A) (circle. x0) (circle. x1))
   40 |                  (to_Id A x0 x1 (from_Id A x0 x1 u2)) u2] [
      ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant to_from_id defined
  
   ￫ info[I0000]
   ￮ constant from_to_Id defined
  


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
  


Unlike the coreflector, the reflector has no counit, so a ♯-locked variable cannot be used directly at its unlocked type.

  $ narya -reflector reflector.ny -e "def ε (A :♯| Type) (x :♯| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def ε (A :♯| Type) (x :♯| A) : A := x
     ^ use of ♯ variable behind id lock requires a key
  
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

  $ narya -spatial spatial.ny -e "def nocounit (A :♯♭| Type) (x :♯♭| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def nocounit (A :♯♭| Type) (x :♯♭| A) : A := x
     ^ use of ♯♭ variable behind id lock requires a key
  
  [1]


  $ narya -spatial spatial.ny -e "def wu2 (x : Type) : (data [ unit2. (_ :♭♯| Type) ]) := unit2. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def wu2 (x : Type) : (data [ unit2. (_ :♭♯| Type) ]) := unit2. x
     ^ use of id variable behind ♭♯ lock requires a key
  
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
  
   ￫ info[I0000]
   ￮ constant ♯ defined
  
   ￫ info[I0000]
   ￮ constant ♯_unit defined
  
   ￫ info[I0000]
   ￮ constant ♯_mult defined
  

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

In the discrete spatial mode theory, ♭ is nonparametric, so a ♭-modal field
disappears at dimensions it filters (the reflexivity/parametric direction).

  $ narya -v -discrete-spatial -parametric discretefields.ny -e 'echo a2'
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant C defined
  
   ￫ info[I0000]
   ￮ constant c defined
  
   ￫ info[I0000]
   ￮ constant c2 defined
  
   ￫ info[I0000]
   ￮ constant p defined
  
   ￫ info[I0000]
   ￮ constant p_test defined
  
   ￫ info[I0000]
   ￮ constant D defined
  
   ￫ info[I0000]
   ￮ constant d defined
  
   ￫ info[I0000]
   ￮ constant cc defined
  
   ￫ info[I0000]
   ￮ constant ♯ defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0000]
   ￮ constant a2 defined
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0000]
   ￮ constant a22 defined
  
  ()
    : ♯⁽ᵉ⁾ (Id A) (_ ≔ (a0 :♭| _) .unsharp) (_ ≔ (a1 :♭| _) .unsharp)
  

At dimension 0 the field projects and computes.

  $ narya -discrete-spatial -parametric discretefields.ny -e "echo p"
  1
    : N
  

Degenerating a stuck modal projection: the projected term stays at the filtered
dimension and the degeneracy is externalized (here as refl), printing
faithfully and round-tripping.

  $ narya -discrete-spatial -parametric discretefields.ny -e "axiom z : C" -e "echo refl ((z :♭| _) .fld)"
  refl ((z :♭| _) .fld)
    : N⁽ᵉ⁾ ((z :♭| _) .fld) ((z :♭| _) .fld)
  

A two-dimensional degeneracy prints with the superscript notation.

  $ narya -discrete-spatial -parametric discretefields.ny -e "axiom z : C" -e "echo sym (refl (refl ((z :♭| _) .fld)))"
  ((z :♭| _) .fld)⁽ᵉᵉ⁾
    : N⁽ᵉᵉ⁾ (refl ((z :♭| _) .fld)) (refl ((z :♭| _) .fld))
        (refl ((z :♭| _) .fld)) (refl ((z :♭| _) .fld))
  

Projecting a disappeared field (from a 1-dimensional element) is an error.

  $ narya -discrete-spatial -parametric discretefields.ny -e "echo (refl c :♭| _) .fld"
   ￫ error[E1713]
   ￭ command-line exec string
   1 | echo (refl c :♭| _) .fld
     ^ field fld does not exist at this dimension: its modality ♭ is nonparametric and filters this dimension away
  
  [1]

Supplying a disappeared field in a tuple/comatch is an error.

  $ narya -discrete-spatial -parametric discretefields.ny -e "def bad : Id C c c ≔ [ .fld ↦ refl (suc. zero.) ]"
   ￫ error[E1714]
   ￭ command-line exec string
   1 | def bad : Id C c c ≔ [ .fld ↦ refl (suc. zero.) ]
     ^ field fld must be omitted at this dimension: its modality ♭ is nonparametric and filters this dimension away
  
  [1]

An ordinary (non-modal) field never disappears: it projects at any dimension.

  $ narya -discrete-spatial -parametric discretefields.ny -e "echo (refl d) .snd"
  refl 0
    : N⁽ᵉ⁾ 0 0
  

If a type is given in a modal field projection, it must be correct.

  $ narya -coreflection -e "def □′ (A :□| Type) : Disc ≔ sig ((x :△| □′ A) .unbox : A)" -e "def unbox (A :△□| Type) (u :△| □′ A) : A ≔ (u :△| Disc) .unbox"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def unbox (A :△□| Type) (u :△| □′ A) : A ≔ (u :△| Disc) .unbox
     ^ term synthesized type
         □′ A
       but is being checked against type
         Disc
       unequal head terms:
         □′
       does not equal
         Disc
  
  [1]

And likewise in a record definition.

  $ narya -coreflection -e "def □′ (A :□| Type) : Disc ≔ sig ((x :△| Disc) .unbox : A)"
   ￫ error[E1508]
   ￭ command-line exec string
   1 | def □′ (A :□| Type) : Disc ≔ sig ((x :△| Disc) .unbox : A)
     ^ invalid self variable type for field unbox: head must be current record
  
  [1]

  $ narya -coreflection -e "def □′ (A :□| Type) : Disc ≔ sig ((x :△| □′ Type) .unbox : A)"
   ￫ error[E1508]
   ￭ command-line exec string
   1 | def □′ (A :□| Type) : Disc ≔ sig ((x :△| □′ Type) .unbox : A)
     ^ invalid self variable type for field unbox: unequal parameters
  
  [1]

Modal higher fields: a ♭-modal higher codatatype (the amazing right adjoint √
composed with ♭).  Since ♭ is parametric, it filters none of the field's
intrinsic dimensions, so projections work at all dimensions, keyed by the
adjunction counit.

  $ narya -v -spatial higherfields.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant √♭A defined
  
   ￫ info[I0001]
   ￮ axiom s0 assumed
  
   ￫ info[I0001]
   ￮ axiom s1 assumed
  
   ￫ info[I0001]
   ￮ axiom s2 assumed
  
  (s2 :♭| _) .root
    : A
  
  (s2 :♭| _) .root
    : A
  
   ￫ info[I0001]
   ￮ axiom s00 assumed
  
   ￫ info[I0001]
   ￮ axiom s01 assumed
  
   ￫ info[I0001]
   ￮ axiom s10 assumed
  
   ￫ info[I0001]
   ￮ axiom s11 assumed
  
   ￫ info[I0001]
   ￮ axiom s02 assumed
  
   ￫ info[I0001]
   ￮ axiom s12 assumed
  
   ￫ info[I0001]
   ￮ axiom s20 assumed
  
   ￫ info[I0001]
   ￮ axiom s21 assumed
  
   ￫ info[I0001]
   ￮ axiom s22 assumed
  
  (s22 :♭| _) .root.1
    : Id A ((s20 :♭| _) .root) ((s21 :♭| _) .root)
  
  (sym s22 :♭| _) .root.1
    : Id A ((s02 :♭| _) .root) ((s12 :♭| _) .root)
  

Constructing a tuple/comatch of a modal higher field is not yet implemented.

  $ narya -spatial higherfields.ny -e "def mk : √♭A ≔ [ .root.e ↦ (mk :♭| _) .root ]"
  (s2 :♭| _) .root
    : A
  
  (s2 :♭| _) .root
    : A
  
  (s22 :♭| _) .root.1
    : Id A ((s20 :♭| _) .root) ((s21 :♭| _) .root)
  
  (sym s22 :♭| _) .root.1
    : Id A ((s02 :♭| _) .root) ((s12 :♭| _) .root)
  
   ￫ error[E0100]
   ￭ command-line exec string
   1 | def mk : √♭A ≔ [ .root.e ↦ (mk :♭| _) .root ]
     ^ unimplemented: tuples/comatches of modal higher fields
  
  [1]

Projecting a modal higher field without the locking annotation is an error.

  $ narya -spatial higherfields.ny -e "echo s2 .root.1"
  (s2 :♭| _) .root
    : A
  
  (s2 :♭| _) .root
    : A
  
  (s22 :♭| _) .root.1
    : Id A ((s20 :♭| _) .root) ((s21 :♭| _) .root)
  
  (sym s22 :♭| _) .root.1
    : Id A ((s02 :♭| _) .root) ((s12 :♭| _) .root)
  
   ￫ error[E1712]
   ￭ command-line exec string
   1 | echo s2 .root.1
     ^ field root is modal with left adjoint ♭, so projecting it requires a locking annotation such as (_ : ♭ | _) .root
  
  [1]

In the discrete spatial mode theory, ♭ is nonparametric, so it filters the
field's intrinsic dimensions; modal higher fields there are not yet supported.

  $ narya -discrete-spatial -parametric -arity 1 -direction d -e "axiom A : Type" -e "def R : Type ≔ codata [ (x :♭| _) .root.d : A ]"
   ￫ error[E0100]
   ￭ command-line exec string
   1 | def R : Type ≔ codata [ (x :♭| _) .root.d : A ]
     ^ unimplemented: nonparametric modal higher fields
  
  [1]
