def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

echo refl 3 : Id ℕ 3 3
