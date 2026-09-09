{` -*- narya-prog-args: ("-proofgeneral" "-monad") -*- `}

def ♯ (A :♯| Type) : Type ≔ data [ box. (_ :♯| A) ]

` The unit η : id ⇒ ♯ lets a plain value supply a ♯-locked field.
def η (A : Type) (x : A) : ♯ A ≔ box. x

` The multiplication μ : ♯∘♯ ⇒ ♯ merges a doubly-boxed value; A needs the composite lock ♯♯
` since forming ♯ (♯ A) requires it, and the merge itself needs the (unique, since b=1) chain of
` multiplications, here just μ itself.
def μ (A :♯♯| Type) (u : ♯ (♯ A)) : ♯ A ≔ match u [ box. (box. y) ↦ box. y ]
