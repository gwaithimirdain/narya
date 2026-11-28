axiom A : Type
axiom B : A → Type
axiom C : Type
axiom S : (X :♭| Type) → ((x :♭| X) → Type) → Type
notation(1) (x :♭| X) "⊗" Y … ≔ S X (x ↦ Y)
axiom ex : ((x :♭| A) → Type) → Type
notation(0) "∃" x "," P … ≔ ex (x ↦ P)
axiom T : (X :♭♯| Type) → ((x :♭♯| X) → Type) → Type
notation(1) (x :♭ ♯| X) "⊠" Y … ≔ T X (x ↦ Y)
