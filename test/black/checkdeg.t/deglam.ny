axiom A : Type
axiom B : A → Type
axiom f : (x : A) → B x

synth refl (x ↦ f x) : Id ((x : A) → B x) f f
echo refl (x ↦ f x) : Id ((x : A) → B x) f f
