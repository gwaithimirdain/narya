  $ narya -v gel.ny
   ￫ info[I0000]
   ￮ constant Gel defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom R assumed
  
   ￫ info[I0001]
   ￮ axiom a₀ assumed
  
   ￫ info[I0001]
   ￮ axiom a₁ assumed
  
   ￫ info[I0001]
   ￮ axiom a₂ assumed
  
   ￫ info[I0001]
   ￮ axiom b₀ assumed
  
   ￫ info[I0001]
   ￮ axiom b₁ assumed
  
   ￫ info[I0001]
   ￮ axiom b₂ assumed
  
   ￫ info[I0001]
   ￮ axiom r₀ assumed
  
   ￫ info[I0001]
   ￮ axiom r₁ assumed
  
   ￫ info[I0001]
   ￮ axiom M assumed
  
  sym M
    : refl Gel A A (refl A) B B (refl B) R R (refl R) a₀ a₁ a₂ b₀ b₁ b₂
        (_ ≔ r₀) (_ ≔ r₁)
  
  sym M .ungel
    : refl R a₀ a₁ a₂ b₀ b₁ b₂ r₀ r₁
  
   ￫ info[I0000]
   ￮ constant eta defined
  
   ￫ info[I0001]
   ￮ axiom A0 assumed
  
   ￫ info[I0001]
   ￮ axiom B0 assumed
  
   ￫ info[I0001]
   ￮ axiom R0 assumed
  
   ￫ info[I0001]
   ￮ axiom A1 assumed
  
   ￫ info[I0001]
   ￮ axiom B1 assumed
  
   ￫ info[I0001]
   ￮ axiom R1 assumed
  
   ￫ info[I0001]
   ￮ axiom A2 assumed
  
   ￫ info[I0001]
   ￮ axiom B2 assumed
  
   ￫ info[I0001]
   ￮ axiom R2 assumed
  
   ￫ info[I0000]
   ￮ constant r_gelr2 defined
  
  r_gelr2
    : Type⁽ᵉᵉ⁾ A0 A1 A2 B0 B1 B2 (Gel A0 B0 R0) (Gel A1 B1 R1)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom b0 assumed
  
   ￫ info[I0001]
   ￮ axiom b1 assumed
  
   ￫ info[I0001]
   ￮ axiom b2 assumed
  
   ￫ info[I0001]
   ￮ axiom r0 assumed
  
   ￫ info[I0001]
   ￮ axiom r1 assumed
  
   ￫ info[I0000]
   ￮ constant r2ty defined
  
   ￫ info[I0001]
   ￮ axiom r2 assumed
  
   ￫ info[I0000]
   ￮ constant r_sym_gelr2 defined
  
  r_sym_gelr2
    : Type⁽ᵉᵉ⁾ A0 B0 (Gel A0 B0 R0) A1 B1 (Gel A1 B1 R1) A2 B2
  
   ￫ info[I0000]
   ￮ constant sym_r2ty defined
  
   ￫ info[I0001]
   ￮ axiom r2' assumed
  
  sym r2
    : sym (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2) a0 b0 (ungel ≔ r0) a1 b1
        (ungel ≔ r1) a2 b2
  
  sym r2'
    : refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 (ungel ≔ r0)
        (ungel ≔ r1)
  
   ￫ info[I0000]
   ￮ constant symsym_r2 defined
  
   ￫ info[I0000]
   ￮ constant symsym_r2_eq_r2 defined
  
   ￫ info[I0000]
   ￮ constant symsym_r2' defined
  
   ￫ info[I0000]
   ￮ constant symsym_r2'_eq_r2' defined
  
  $ narya gel.ny -e "def r2ty_eq_sym_r2ty : Id Type r2ty sym_r2ty := refl r2ty"
  sym M
    : refl Gel A A (refl A) B B (refl B) R R (refl R) a₀ a₁ a₂ b₀ b₁ b₂
        (_ ≔ r₀) (_ ≔ r₁)
  
  sym M .ungel
    : refl R a₀ a₁ a₂ b₀ b₁ b₂ r₀ r₁
  
  r_gelr2
    : Type⁽ᵉᵉ⁾ A0 A1 A2 B0 B1 B2 (Gel A0 B0 R0) (Gel A1 B1 R1)
  
  r_sym_gelr2
    : Type⁽ᵉᵉ⁾ A0 B0 (Gel A0 B0 R0) A1 B1 (Gel A1 B1 R1) A2 B2
  
  sym r2
    : sym (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2) a0 b0 (ungel ≔ r0) a1 b1
        (ungel ≔ r1) a2 b2
  
  sym r2'
    : refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 (ungel ≔ r0)
        (ungel ≔ r1)
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def r2ty_eq_sym_r2ty : Id Type r2ty sym_r2ty := refl r2ty
     ^ term synthesized type
         refl Type
           (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 (ungel ≔ r0)
              (ungel ≔ r1))
           (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 (ungel ≔ r0)
              (ungel ≔ r1))
       but is being checked against type
         refl Type
           (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 (ungel ≔ r0)
              (ungel ≔ r1))
           (sym (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2) a0 b0 (ungel ≔ r0) a1 b1
              (ungel ≔ r1) a2 b2)
       unequal terms:
         refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2 a0 a1 a2 b0 b1 b2 (ungel ≔ r0)
           (ungel ≔ r1)
       does not equal
         sym (refl Gel A0 A1 A2 B0 B1 B2 R0 R1 R2) a0 b0 (ungel ≔ r0) a1 b1
           (ungel ≔ r1) a2 b2
  
  [1]
