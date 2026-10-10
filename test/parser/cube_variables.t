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
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B b b
  
  {x00} {x01} {x02} {x10} {x11} {x12} {x20} {x21} x22 ↦ b⁽ᵉᵉ⁾
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl b) (refl b) (refl b) (refl b)
  
  x ⤇ refl b
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B b b
  
  x ⤇ b⁽ᵉᵉ⁾
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl b) (refl b) (refl b) (refl b)
  
  {x0} {x1} x2 ↦ h x0
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B b b
  
  x ⤇ h x.0
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B b b
  
  x ⤇ ap h x.02
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl b) (refl b) (h 𝑥₀₀) (h 𝑥₀₁)
  
  x ⤇ ap h x.02
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ (refl b) (refl b) (h 𝑥₀₀) (h 𝑥₀₁)
  
  refl b
    : Id B b b
  
