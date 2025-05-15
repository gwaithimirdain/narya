axiom A : Type
axiom B : A → Type
axiom C : A → Type

def D : Type ≔ data [ con. (a : A) (f : B a → C a) ]

def get_a (d : D) : A ≔ match d [ con. a f ↦ a ]

def get_f (d : D) (b : B (get_a d)) : C (get_a d) ≔ match d [
| con. a f ↦ f b]
