axiom A : Type

synth (x : A) ↦ x

axiom B : A → Type

axiom C : A → Type

axiom f : (x : A) → B x

axiom g : (x : A) → B x → C x

synth (x : A) ↦ g x (f x)

axiom a : A

echo ((x : A) ↦ x) a

echo ((x : A) ↦ g x (f x)) a

def unit : Type ≔ sig ()

echo ((x : A) ↦ ()) : A → unit
