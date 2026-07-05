axiom A : Type

def foo : Type ≔ codata [
| x .f : A
| x .f.e : A → A ]
