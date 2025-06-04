axiom A : Type
axiom B : A → Type
axiom a0 : A
axiom a1 : A
axiom a2 : Id A a0 a1
axiom b0 : B a0
axiom b1 : B a1
axiom b2 : refl B a0 a1 a2 b0 b1
