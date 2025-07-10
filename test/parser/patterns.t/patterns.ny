def Sum (A B : Type) : Type ≔ data [ left. (_ : A) | right. (_ : B) ]
notation(0) "$" x ≔ left. x
notation(0) y "@" ≔ right. y

def swap (A : Type) (x : Sum A A) : Sum A A ≔ match x [
| $ x ↦ x @
| y @ ↦ $ y]

def Triple (A : Type) : Type ≔ data [ foo. (_ : A) (_ : A) (_ : A) ]
notation(0) x "+" y "+" z ≔ foo. x y z

def flop (A : Type) (x : Triple A) : Triple A ≔ match x [
| a + b + c ↦ c + a + b]

axiom A : Type
axiom a : A
axiom b : A
axiom c : A

echo flop A (a + c + b)

def assoc (A B C : Type) (x : Sum (Sum A B) C) : Sum A (Sum B C)
  ≔ match x [ $ ($ a) ↦ $ a | $ (b @) ↦ ($ b) @ | c @ ↦ (c @) @ ]
