def prod (X Y : Type) : Type ≔ sig ( fst : X, snd : Y )

notation(2) X "×" Y ≔ prod X Y

axiom B : Type
axiom b : B
axiom C : Type
axiom c : C

echo ((b,c) : B × C) .fst
