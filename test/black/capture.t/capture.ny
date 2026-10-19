axiom A : Type
axiom B : Type

` A variable bound in a term being displayed, whose name would capture a constant mentioned in its scope, is renamed.
def F (X : Type) : Type ≔ (A : X) → X
echo F A

def G (X : Type) : Type ≔ (A : X) (A′ : X) → X
echo G A

` But it is not renamed if the constant isn't mentioned in its scope.
def H (X : Type) : Type ≔ (A : X) → B
echo H A

` The prefix _root_ refers to a constant shadowed by a local variable.
echo (A : A) → _root_.A
