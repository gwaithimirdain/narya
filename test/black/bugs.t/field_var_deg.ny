axiom A : Type
axiom c : A
def T : Type := sig ( x : A, q : Id (Id A x x) (refl x) (refl x), s : Id (Id A c c) (refl c) (refl c), t : Id (Id (Id A x x) (refl x) (refl x)) q s)
