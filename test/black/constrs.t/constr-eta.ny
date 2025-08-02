def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def suc : ℕ → ℕ ≔ suc.

echo suc (suc (suc 0))

def kinetic_suc : ℕ → ℕ ≔ ((x : ℕ → ℕ) ↦ x : ℕ → ℕ) suc.

{` TODO: Get a generic variable name for this. `}
echo kinetic_suc

def refl_suc : {n₀ n₁ : ℕ} (n₂ : Id ℕ n₀ n₁) →⁽ᵉ⁾ Id ℕ (suc. n₀) (suc. n₁)
  ≔ suc.

def Vec (A : Type) : ℕ → Type ≔ data [
| nil. : Vec A 0
| cons. (n : ℕ) (x : A) (xs : Vec A n) : Vec A (suc n) ]

def cons3 (A : Type) : (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)
  ≔ cons.

def cons2 (A : Type) (n : ℕ) : (x : A) (xs : Vec A n) → Vec A (suc n)
  ≔ cons. n

def cons1 (A : Type) (n : ℕ) (x : A) : (xs : Vec A n) → Vec A (suc n)
  ≔ cons. n x

axiom A : Type
axiom a : A

echo cons3 A 2 a (cons2 A 1 a (cons1 A 0 a nil.))
