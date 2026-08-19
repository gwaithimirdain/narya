def N : Type ≔ data [ zero. | suc. (_ : N) ]

` The motive says the branches have type Type, but the constant W takes an
` index, so the constructor outputs have one argument too many.  This used to
` be an anomaly rather than a user-facing error.
def W (n : N) : N → Type ≔ match n return _ ↦ Type [
| zero. ↦ data [ w0. : W n zero. ]
| suc. m ↦ data [ w1. : W n (suc. m) ]
]
