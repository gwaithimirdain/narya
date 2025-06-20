  $ narya degnotn.ny
  refl a
    : Id A a a
  
  Id A a0 a1
    : Type
  
  ap f
    : {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Id C (f H₀) (f H₁)
  
  Id B
    : {H₀ : A} {H₁ : A} (H₂ : Id A H₀ H₁) →⁽ᵉ⁾ Type⁽ᵉ⁾ (B H₀) (B H₁)
  
  Unit⁽ᵉ⁾ u0 u1
    : Type
  
