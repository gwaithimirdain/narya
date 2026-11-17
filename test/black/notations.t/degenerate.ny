{` A notation keyed to a degeneracy of a type, displayed for exactly its full instantiations `}
axiom A : Type
axiom x : A
axiom y : A
notation(0) x "=" y ≔ Id (_ : Type) x y
echo x = y
echo Id A x y
axiom p : x = y
echo p
echo refl x

{` It is used for canonical types and the universe too `}
def Nat : Type ≔ data [ zero. | suc. (n : Nat) ]
axiom n : Nat
echo Id Nat n zero.
echo Id Type A A

{` and inside higher function-types `}
axiom f : A → A
echo Id (A → A) f f

{` but not when neither argument synthesizes, since then the omitted type couldn't be solved for `}
echo Id Nat zero. zero.

{` nor for a degeneracy of a type family, whose arguments are application arguments rather than instantiation arguments `}
axiom B : Type
axiom F : A → B → Type
axiom b₀ : B
axiom b₁ : B
axiom b₂ : Id B b₀ b₁
echo Id F p b₂

{` nor for higher degeneracies, or partial instantiations of them `}
echo Id (Id A x y) p p
echo A⁽ᵉᵉ⁾

{` Any name of the degeneracy defines the same notation, and the operand can be a variable `}
notation(0) x "≡" y "∈" X ≔ refl (X : Type) x y
echo x = y
echo Id F p b₂
