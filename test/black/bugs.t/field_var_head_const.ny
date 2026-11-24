axiom A : Type
axiom c : A
def T : Type := sig ( x : A, p : Id A x x, q : Id A c c, r : Id (Id A x x) p q)
