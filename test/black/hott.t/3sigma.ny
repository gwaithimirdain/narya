{` Transport and lifting compute on ternary Σ-types `}

def Σ3 (A : Type) (B : A → Type) (C : (x : A) → B x → Type) : Type ≔ sig (
  fst : A,
  snd : B fst,
  thd : C fst snd )

axiom A₀ : Type
axiom A₁ : Type
axiom A₂ : Id Type A₀ A₁
axiom B₀ : A₀ → Type
axiom B₁ : A₁ → Type
axiom B₂ : Id ((X ↦ X → Type) : Type → Type) A₂ B₀ B₁
axiom C₀ : (x₀ : A₀) → B₀ x₀ → Type
axiom C₁ : (x₁ : A₁) → B₁ x₁ → Type
axiom C₂
  : Id ((X Y ↦ (x : X) → Y x → Type) : (X : Type) → (X → Type) → Type) A₂
      B₂ C₀ C₁

axiom u₀ : Σ3 A₀ B₀ C₀

echo refl Σ3 A₂ B₂ C₂ .trr u₀
echo refl Σ3 A₂ B₂ C₂ .trr u₀ .fst
echo refl Σ3 A₂ B₂ C₂ .trr u₀ .snd
echo refl Σ3 A₂ B₂ C₂ .trr u₀ .thd

echo refl Σ3 A₂ B₂ C₂ .liftr u₀
echo refl Σ3 A₂ B₂ C₂ .liftr u₀ .fst
echo refl Σ3 A₂ B₂ C₂ .liftr u₀ .snd
echo refl Σ3 A₂ B₂ C₂ .liftr u₀ .thd

