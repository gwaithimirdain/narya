{` -*- narya-prog-args: ("-proofgeneral" "-reflector") -*- `}

def ♯ (A :♯| Type) : Type ≔ data [ ♯. (_ :♯| A) ]

def ♯map (A B :♯| Type) (f :♯| A → B) : ♯ A → ♯ B ≔ [
| ♯. x ↦ ♯. (f x)]

` def ε (A :♯| Type) (x :♯| A) : A := x

axiom A : Type
axiom a : A

def η (x : A) : ♯ A ≔ ♯. x

def ηη (x : A) : ♯ (♯ A) ≔ ♯. (♯. x)
