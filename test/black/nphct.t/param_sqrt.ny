{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

def √ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x : Γ)
  : Type
  ≔ codata [
| s .root.p : A x.0 x.1 x.2
| s .else : B x ]
