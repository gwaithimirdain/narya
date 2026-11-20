axiom A : Type
axiom B : A → Type
axiom C : Type
axiom a : A
def Σ (X : Type) (Y : X → Type) : Type ≔ sig (fst : X, snd : Y fst)
notation(1) (x : X) "×" Y … ≔ Σ X (x ↦ Y)
axiom ex : (A → Type) → Type
notation(0) "∃" x "," P … ≔ ex (x ↦ P)
