{` -*- narya-prog-args: ("-proofgeneral" "-dtt") -*- `}

{` General displayed coinductives `}

def dCoind (Φ : △ □ | Type) (A : △ □ | Φ → Type)
  (B : △ □ | (φ : Φ) (a : A φ) → Type)
  (σ : △ □ | (φ : Φ) (a : A φ) (b : B φ a) → Φ⁽ᵈ⁾ φ) (φ : Φ)
  : Type
  ≔ codata [
| x .head : A φ
| x .tail : (b : B φ (x .head)) → dCoind⁽ᵈ⁾ Φ A B σ (σ φ (x .head) b) x ]
