def isFibrant : Type → Type ≔ A ↦ codata [
| x .trr.e : A.0 → A.1
| x .liftr.e : (x₀ : A.0) → A.2 x₀ (x.2 .trr x₀)
| x .trl.e : A.1 → A.0
| x .liftl.e : (x₁ : A.1) → A.2 (x.2 .trl x₁) x₁
| x .id.e : (x₀ : A.0) (x₁ : A.1) → isFibrant (A.2 x₀ x₁) ]
