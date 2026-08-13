  $ narya constr-eta.ny
  3
    : ℕ
  
  𝑥 ↦ suc. 𝑥
    : ℕ → ℕ
  
  cons. 2 a (cons. 1 a (cons. 0 a nil.))
    : Vec A 3
  

The redundant boundary arguments of a higher-dimensional constructor can be supplied in braces, as checked documentation.

  $ narya constr-boundary.ny
  suc. n₂
    : ℕ⁽ᵉ⁾ (suc. n₀) (suc. n₁)
  
  suc. n₂
    : ℕ⁽ᵉ⁾ (suc. n₀) (suc. n₁)
  
  pair. n₂ n₂
    : P⁽ᵉ⁾ (pair. n₀ n₀) (pair. n₁ n₁)
  
  suc. (refl n₂)
    : ℕ⁽ᵉᵉ⁾ {suc. n₀} {suc. n₀} (suc. (refl n₀)) {suc. n₁} {suc. n₁}
        (suc. (refl n₁)) (suc. n₂) (suc. n₂)
  

They have to match the boundary determined by the type.

  $ narya boundary.ny -e 'def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₀} n₂'
   ￫ error[E1003]
   ￭ command-line exec string
   1 | def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₀} n₂
     ^ supplied 1-boundary argument
         n₀
       doesn't match the one determined by the type
         n₁
       unequal head constants:
         n₀
       does not equal
         n₁
  
  [1]

It's all or nothing: either every face of an argument is documented, or none is.

  $ narya boundary.ny -e 'def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} n₂'
   ￫ error[E0702]
   ￭ command-line exec string
   1 | def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} n₂
     ^ unexpected explicit argument: expecting implicit argument of constructor suc
  
  [1]

  $ narya boundary.ny -e 'def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₁} {n₁} n₂'
   ￫ error[E0702]
   ￭ command-line exec string
   1 | def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₁} {n₁} n₂
     ^ unexpected implicit argument: expecting explicit primary argument of constructor suc
  
  [1]

  $ narya boundary.ny -e 'def bad : ℕ ≔ suc. {n₀} n₀'
   ￫ error[E0702]
   ￭ command-line exec string
   1 | def bad : ℕ ≔ suc. {n₀} n₀
     ^ unexpected implicit argument: expecting explicit primary argument of constructor suc
  
  [1]

Boundary arguments must be followed by the explicit argument they belong to.

  $ narya boundary.ny -e 'def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₁}'
   ￫ error[E1001]
   ￭ command-line exec string
   1 | def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₁}
     ^ not enough arguments to constructor suc (need 1 more)
  
  [1]
