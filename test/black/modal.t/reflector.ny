{` -*- narya-prog-args: ("-proofgeneral" "-reflector") -*- `}

def diamond (A :♯| Type) : Type ≔ data [ diamond. (x :♯| A) ]

def diamondmap (A B :♯| Type) (f :♯| A → B) : diamond A → diamond B ≔ [
| diamond. x ↦ diamond. (f x)]

` def ε (A :♯| Type) (x :♯| A) : A := x

axiom A : Type
axiom a : A

def η (x : A) : diamond A ≔ diamond. x

def ηη (x : A) : diamond (diamond A) ≔ diamond. (diamond. x)
