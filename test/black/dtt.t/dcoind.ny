{` -*- narya-prog-args: ("-proofgeneral" "-dtt") -*- `}

def disp (X :△□| Type) (x : X) : Type
  ≔ ((Y ↦ Y) : ((_ :△□| Type) → Type))⁽ᵈ⁾ X x

{` General displayed coinductives `}

def dCoind (Φ : △ □ | Type) (A : △ □ | Φ → Type)
  (B : △ □ | (φ : Φ) (a : A φ) → Type)
  (σ : △ □ | (φ : Φ) (a : A φ) (b : B φ a) → disp Φ φ) (φ : Φ)
  : Type
  ≔ codata [
| x .head : A φ
| x .tail : (b : B φ (x .head)) → dCoind⁽ᵈ⁾ Φ A B σ (σ φ (x .head) b) x ]
