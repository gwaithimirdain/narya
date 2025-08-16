def Prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )

axiom A : Type
axiom B : Type
axiom a : A
axiom b : B

echo refl (a, b) : Id (Prod A B) (a, b) (a, b)
echo refl (fst ≔ a, snd ≔ b) : Id (Prod A B) (a, b) (a, b)
echo refl (snd ≔ b, fst ≔ a) : Id (Prod A B) (a, b) (a, b)
