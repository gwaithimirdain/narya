{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

def √ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x : Γ)
  : Type
  ≔ codata [
| s .root.p : A x.0 x.1 x.2
| s .else : B x ]

def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )

notation(2) A "×" B ≔ prod A B

def Γhat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type)
  : Type
  ≔ sig (
  x0 : Γ,
  x1 : Γ,
  x2 : Br Γ x0 x1,
  u0 : √ Γ A B x0,
  u1 : √ Γ A B x1 )

def id_√ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : Br Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1)
  : Type
  ≔ √ (Γhat Γ A B)
       (y0 y1 y2 ↦ Br A (y0 .x2) (y1 .x2) (sym (y2 .x2)) (y2 .u0 .fst) (y2 .u1 .fst))
       (y ↦ A (y .x0) (y .x1) (y .x2) × Br B (y .x2) (y .u0 .snd) (y .u1 .snd))
       (x0, x1, x2, u0, u1)
