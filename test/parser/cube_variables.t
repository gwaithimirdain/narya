Testing parsing and printing of cube variables

  $ cat >cube_vars.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom b:B
  > def f : A -> B := x |-> b
  > def g (x:A) : B := b
  > def fg : Id (A -> B) f g := {x0} {x1} x2 |-> refl b
  > echo ({x0} {x1} x2 |-> fg x2) : Id (A -> B) f g
  > echo ({x00} {x01} {x02} {x10} {x11} {x12} {x20} {x21} x22 |-> refl fg x22) : Id (Id (A -> B) f g) fg fg
  > echo (x |=> fg x.2) : Id (A -> B) f g
  > echo ((x |=> refl fg x.22) : Id (Id (A -> B) f g) fg fg)
  > axiom h (x:A) : Id B b b
  > def fgh : Id (A -> B) f g := {x0} {x1} x2 |-> h x0
  > echo ({x0} {x1} x2 |-> fgh x2) : Id (A -> B) f g
  > echo (x |=> fgh x.2) : Id (A -> B) f g
  > echo ((x |=> refl fgh x.22) : Id (Id (A -> B) f g) fgh fgh)
  > echo ((x |=> refl h x.02) : Id (Id (A -> B) f g) fgh fgh)
  > axiom a0:A
  > axiom a1:A
  > axiom a2:Id A a0 a1
  > echo refl f a2
  > EOF

  $ narya cube_vars.ny
  {x0} {x1} x2 ↦ refl b
    : {H₀ : A} {H₁ : A} (H₂ : refl A H₀ H₁) ⇒ refl B b b
  
  {x00} {x01} {x02} {x10} {x11} {x12} {x20} {x21} x22 ↦ b⁽ᵉᵉ⁾
    : {H₀₀ : A} {H₀₁ : A} {H₀₂ : refl A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
      {H₁₂ : refl A H₁₀ H₁₁} {H₂₀ : refl A H₀₀ H₁₀} {H₂₁ : refl A H₀₁ H₁₁}
      (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
      ⇒ B⁽ᵉᵉ⁾ (refl b) (refl b) (refl b) (refl b)
  
  x ⤇ refl b
    : {H₀ : A} {H₁ : A} (H₂ : refl A H₀ H₁) ⇒ refl B b b
  
  x ⤇ b⁽ᵉᵉ⁾
    : {H₀₀ : A} {H₀₁ : A} {H₀₂ : refl A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
      {H₁₂ : refl A H₁₀ H₁₁} {H₂₀ : refl A H₀₀ H₁₀} {H₂₁ : refl A H₀₁ H₁₁}
      (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
      ⇒ B⁽ᵉᵉ⁾ (refl b) (refl b) (refl b) (refl b)
  
  {x0} {x1} x2 ↦ h x0
    : {H₀ : A} {H₁ : A} (H₂ : refl A H₀ H₁) ⇒ refl B b b
  
  x ⤇ h x.0
    : {H₀ : A} {H₁ : A} (H₂ : refl A H₀ H₁) ⇒ refl B b b
  
  x ⤇ refl h x.02
    : {H₀₀ : A} {H₀₁ : A} {H₀₂ : refl A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
      {H₁₂ : refl A H₁₀ H₁₁} {H₂₀ : refl A H₀₀ H₁₀} {H₂₁ : refl A H₀₁ H₁₁}
      (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
      ⇒ B⁽ᵉᵉ⁾ (refl b) (refl b) (h H₀₀) (h H₀₁)
  
  x ⤇ refl h x.02
    : {H₀₀ : A} {H₀₁ : A} {H₀₂ : refl A H₀₀ H₀₁} {H₁₀ : A} {H₁₁ : A}
      {H₁₂ : refl A H₁₀ H₁₁} {H₂₀ : refl A H₀₀ H₁₀} {H₂₁ : refl A H₀₁ H₁₁}
      (H₂₂ : A⁽ᵉᵉ⁾ H₀₂ H₁₂ H₂₀ H₂₁)
      ⇒ B⁽ᵉᵉ⁾ (refl b) (refl b) (h H₀₀) (h H₀₁)
  
  refl b
    : refl B b b
  
