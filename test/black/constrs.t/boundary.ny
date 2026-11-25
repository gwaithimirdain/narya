def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def P : Type ≔ data [ pair. (x : ℕ) (y : ℕ) ]

axiom n₀ : ℕ

axiom n₁ : ℕ

axiom n₂ : Id ℕ n₀ n₁
