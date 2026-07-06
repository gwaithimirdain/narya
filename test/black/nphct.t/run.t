Higher coinductive types with filtering-modal (♭) parameters: the ♭ parameter is
not degenerated in the contexts of higher fields, so field types can refer to it
directly, and its instances construct and project as expected.

  $ narya -v -parametric -discrete-coreflector nphct.ny
   ￫ info[I0000]
   ￮ constant ♭√ defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom s0 assumed
  
   ￫ info[I0001]
   ￮ axiom s1 assumed
  
   ￫ info[I0001]
   ￮ axiom s2 assumed
  
  s2 .root
    : A
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant √a defined
  
  a
    : A
  
   ￫ info[I0000]
   ￮ constant ♭√√ defined
  
   ￫ info[I0000]
   ￮ constant √√a defined
  
  a
    : A
  

Without the modality, an ordinary parameter IS degenerated in the higher field's
context, so the same field type fails to check: the parameter A becomes a square
of type Type⁽ᵉ⁾ A.0 A.1, which is not a Type.

  $ narya -parametric -discrete-coreflector -e "def sqrt (A : Type) : Type ≔ codata [ x .root.e : A ]"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def sqrt (A : Type) : Type ≔ codata [ x .root.e : A ]
     ^ term synthesized type
         Type⁽ᵉ⁾ A.0 A.1
       but is being checked against type
         Type
       unequal head terms:
         Type⁽ᵉ⁾
       does not equal
         Type
  
  [1]

  $ narya -v -parametric -discrete-coreflector -direction p,rel,Br param_sqrt.ny
   ￫ info[I0000]
   ￮ constant eq defined
  
   ￫ info[I0000]
   ￮ constant eq.ap defined
  
   ￫ info[I0000]
   ￮ constant eqv defined
  
   ￫ info[I0002]
   ￮ notation «_ ≅ _» defined
  
   ￫ info[I0000]
   ￮ constant eqd defined
  
   ￫ info[I0000]
   ￮ constant eq2d defined
  
   ￫ info[I0000]
   ￮ constant eqd2d defined
  
   ￫ info[I0000]
   ￮ constant Id_eq′ defined
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0002]
   ￮ notation «_ × _» defined
  
   ￫ info[I0000]
   ￮ constant √ defined
  
   ￫ info[I0000]
   ￮ constant eq_√ defined
  
   ￫ info[I0001]
   ￮ axiom √_ext assumed
  
   ￫ info[I0000]
   ￮ constant Γhat defined
  
   ￫ info[I0000]
   ￮ constant Ahat defined
  
   ￫ info[I0000]
   ￮ constant Bhat defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/param_sqrt.ny
   108 |       [ .fst.p ↦ rfl. | .snd ↦ rfl. ],
       ^ comatch encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant id_√_iso defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     Γ :♭| Type
     A :♭| (x₀ : Γ) (x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type
     B :♭| Γ → Type
     x0 : Γ
     x1 : Γ
     x2 : Br Γ x0 x1
     u0 : √ Γ A B x0
     u1 : √ Γ A B x1
     u2 : √⁽ᵖ⁾ Γ A B x2 u0 u1
     ----------------------------------------------------------------------
     eq (√⁽ᵖ⁾ Γ A B x2 u0 u1)
       (id_√_iso Γ A B x0 x1 x2 u0 u1 .to (id_√_iso Γ A B x0 x1 x2 u0 u1 .fro u2))
       u2
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     Γ :♭| Type
     A :♭| (x₀ : Γ) (x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type
     B :♭| Γ → Type
     x0 : Γ
     x1 : Γ
     x2 : Br Γ x0 x1
     u0 : √ Γ A B x0
     u1 : √ Γ A B x1
     ----------------------------------------------------------------------
     (a : √ (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1))
     → eq
         (eq (√⁽ᵖ⁾ Γ A B x2 u0 u1)
            (id_√_iso Γ A B x0 x1 x2 u0 u1
             .to
               (id_√_iso Γ A B x0 x1 x2 u0 u1
                .fro (id_√_iso Γ A B x0 x1 x2 u0 u1 .to a)))
            (id_√_iso Γ A B x0 x1 x2 u0 u1 .to a))
         (eq.ap (√ (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1))
            (√⁽ᵖ⁾ Γ A B x2 u0 u1) (id_√_iso Γ A B x0 x1 x2 u0 u1 .to)
            (id_√_iso Γ A B x0 x1 x2 u0 u1
             .fro (id_√_iso Γ A B x0 x1 x2 u0 u1 .to a)) a
            (√_ext (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1)
               (x0, x1, x2, u0, u1) rfl.
               (id_√_iso Γ A B x0 x1 x2 u0 u1
                .fro (id_√_iso Γ A B x0 x1 x2 u0 u1 .to a)) a _comatch.F0.0{…}))
         (id_√_iso Γ A B x0 x1 x2 u0 u1
          .to_fro (id_√_iso Γ A B x0 x1 x2 u0 u1 .to a))
  
   ￫ error[E3002]
   ￮ file param_sqrt.ny contains open holes
  
  [1]

