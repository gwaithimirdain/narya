def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

echo refl 3 : Id ℕ 3 3

echo 3⁽ᵉᵉ⁾ : Id (Id ℕ) {3} {3} 3 {3} {3} 3 3 3

echo refl (refl 3) : Id (Id ℕ) {3} {3} 3 {3} {3} 3 3 3
