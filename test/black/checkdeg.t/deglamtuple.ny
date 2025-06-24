def Prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )
axiom A : Type
axiom B : A → Type
axiom C : A → Type
axiom f : (x : A) → B x
axiom g : (x : A) → C x

synth refl (x ↦ (f x, g x))
      : Id ((x : A) → Prod (B x) (C x)) (x ↦ (f x, g x)) (x ↦ (f x, g x))
echo refl (x ↦ (f x, g x))
     : Id ((x : A) → Prod (B x) (C x)) (x ↦ (f x, g x)) (x ↦ (f x, g x))

synth refl (x ↦ f x, x ↦ g x)
      : Id (Prod ((x : A) → (B x)) ((x : A) → (C x))) (f, g) (f, g)
echo refl (x ↦ f x, x ↦ g x)
     : Id (Prod ((x : A) → (B x)) ((x : A) → (C x))) (f, g) (f, g)
