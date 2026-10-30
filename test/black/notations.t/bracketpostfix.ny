{` A left-open notation that is a prefix of left-closed ones whose trees are recursive, here the notations starting with a bracket. `}
axiom A : Type
axiom f : A → A
notation(1) x "[" ≔ f x
def y : A → A ≔ x ↦ x [
def p : A → A ≔ [ x ↦ x ]
axiom a : A
echo y a
echo p a
