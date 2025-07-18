  $ cat >test.ny <<EOF
  > axiom A:Type
  > axiom a0:A
  > axiom a1:A
  > axiom a2: Id A a0 a1
  > def a2' := refl ((y ↦ let id : A → A ≔ x ↦ x in id y) : A → A)
  > echo a2'
  > EOF

  $ narya -v test.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0000]
   ￮ constant a2' defined
  
  y ⤇ y.2
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id A 𝑥₀ 𝑥₁
  
