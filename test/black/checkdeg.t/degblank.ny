axiom A : Type

axiom a : A

synth refl _ : Id A a a

synth _⁽ᵉ⁾ : Id A a a

synth refl (refl _) : Id (Id A) (refl a) (refl a) (refl a) (refl a)

echo refl (refl _) : Id (Id A) (refl a) (refl a) (refl a) (refl a)

echo refl (refl _)
     : Id (Id A) {a} {a} (refl _) {a} {a} (refl _) (refl _) (refl _)

axiom a0 : A
axiom a1 : A
axiom a2 : Id A a0 a1

echo refl _ : Id (Id A) (refl a0) (refl a1) a2 a2
