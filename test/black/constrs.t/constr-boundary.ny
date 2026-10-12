def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def P : Type ≔ data [ pair. (x : ℕ) (y : ℕ) ]

axiom n₀ : ℕ

axiom n₁ : ℕ

axiom n₂ : Id ℕ n₀ n₁

{` The boundary arguments of a higher-dimensional constructor application are ordinarily
extracted from the type, but they can also be supplied in braces as checked documentation. `}
def s₂ : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₁} n₂

{` Omitting them means the same thing, and elaborates to the same term. `}
def s₂′ : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. n₂

echo s₂

echo s₂′

{` Each argument decides separately whether to document its boundary. `}
def q : Id P (pair. n₀ n₀) (pair. n₁ n₁) ≔ pair. {n₀} {n₁} n₂ n₂

echo q

{` It works at higher dimensions too, where the boundary arguments come in the same order as
the instantiation arguments of the type. `}
def s₄
  : ℕ⁽ᵉᵉ⁾ {suc. n₀} {suc. n₀} (suc. n₀⁽ᵉ⁾) {suc. n₁} {suc. n₁} (suc. n₁⁽ᵉ⁾)
      (suc. n₂) (suc. n₂)
  ≔ suc. {n₀} {n₀} {n₀⁽ᵉ⁾} {n₁} {n₁} {n₁⁽ᵉ⁾} {n₂} {n₂} n₂⁽ᵉ⁾

echo s₄
