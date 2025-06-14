axiom A : Type
axiom B : A → Type
axiom f : (x : A) → B x
axiom g : (x : A) → B x

def idok
  : Id Type (Id ((x : A) → B x) f g)
      ({x₀ : A} {x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁))
  ≔ refl (Id ((x : A) → B x) f g)

axiom f00 : (x : A) → B x
axiom f01 : (x : A) → B x
axiom f10 : (x : A) → B x
axiom f11 : (x : A) → B x

axiom f02 : Id ((x : A) → B x) f00 f01
axiom f12 : Id ((x : A) → B x) f10 f11
axiom f20 : Id ((x : A) → B x) f00 f10
axiom f21 : Id ((x : A) → B x) f01 f11

def id2ok
  : Id Type (((x : A) → B x)⁽ᵉᵉ⁾ f02 f12 f20 f21)
      ({x₀₀ : A} {x₀₁ : A} {x₀₂ : refl A x₀₀ x₀₁} {x₁₀ : A} {x₁₁ : A}
       {x₁₂ : refl A x₁₀ x₁₁} {x₂₀ : refl A x₀₀ x₁₀} {x₂₁ : refl A x₀₁ x₁₁}
       (x₂₂ : A⁽ᵉᵉ⁾ x₀₂ x₁₂ x₂₀ x₂₁)
       →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ x₂₂ (f02 x₀₂) (f12 x₁₂) (f20 x₂₀) (f21 x₂₁))
  ≔ refl (((x : A) → B x)⁽ᵉᵉ⁾ f02 f12 f20 f21)

def nidok
  : Id (Id Type ((x : A) → B x) ((x : A) → B x)) (Id ((x : A) → B x))
      ((x : Id A) ⇒ Id B x.2)
  ≔ refl (Id ((x : A) → B x))
