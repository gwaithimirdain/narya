{` Projecting a field from a transport in a 3-dimensional degeneracy of a record type `}
def R (A : Type) : Type ≔ sig ( fst : A )
def S (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )
axiom A : Type
axiom B : A → Type
axiom x : A
axiom u : B x
echo refl (Id (Id (R A) (x,) (x,)) (refl (x,)) (refl (x,))) .trr (x,)⁽ᵉᵉ⁾ .fst
echo refl (Id (Id (R A) (x,) (x,)) (refl (x,)) (refl (x,))) .liftr (x,)⁽ᵉᵉ⁾ .fst
echo refl (Id (Id (Id (R A) (x,) (x,)) (refl (x,)) (refl (x,))) (refl (refl (x,))) (refl (refl (x,)))) .trr (x,)⁽ᵉᵉᵉ⁾ .fst
echo refl (Id (Id (S A B) (x,u) (x,u)) (refl (x,u)) (refl (x,u))) .trr (x,u)⁽ᵉᵉ⁾ .snd
