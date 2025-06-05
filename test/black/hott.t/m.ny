{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

{` Transport and lifting compute on M-types `}

def M (A : Type) (B : A → Type) : Type ≔ codata [
| x .recv : A
| x .send : B (x .recv) → M A B ]

axiom A₀ : Type
axiom A₁ : Type
axiom A₂ : Id Type A₀ A₁
axiom B₀ : A₀ → Type
axiom B₁ : A₁ → Type
axiom B₂ : Id ((X ↦ X → Type) : Type → Type) A₂ B₀ B₁

axiom u₀ : M A₀ B₀

echo refl M A₂ B₂ .trr u₀
echo refl M A₂ B₂ .trr u₀ .recv
axiom b₁ : B₁ (A₂ .trr (u₀ .recv))
echo refl M A₂ B₂ .trr u₀ .send b₁

echo refl M A₂ B₂ .liftr u₀
echo refl M A₂ B₂ .liftr u₀ .recv
axiom b₀ : B₀ (u₀ .recv)
axiom b₂ : B₂ (A₂ .liftr (u₀ .recv)) b₀ b₁
echo refl M A₂ B₂ .liftr u₀ .send b₂

synth M⁽ᵉᵉ⁾ A₂⁽¹ᵉ⁾ B₂⁽¹ᵉ⁾
          (refl u₀
           .send
             (B₂⁽ᵉ¹⁾ (sym (refl A₂ .liftr.1 (refl u₀ .recv))) b₂
                  (B₂ (A₂ .liftr.1 (u₀ .recv)) .liftl.1 b₁)
              .trl.1 (refl b₁)))
          (M⁽ᵉᵉ⁾ A₂⁽¹ᵉ⁾ B₂⁽¹ᵉ⁾
           .trr.1
             (refl u₀
              .send
                (B₂⁽¹ᵉ⁾ (refl A₂ .liftr.1 (refl u₀ .recv)) .trl.1 (refl b₁))))
  .trl.1
    (refl M A₂ B₂ .liftr.1 (u₀ .send (B₂ (A₂ .liftr.1 (u₀ .recv)) .trl.1 b₁)))
