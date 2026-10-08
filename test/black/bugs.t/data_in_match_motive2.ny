def N : Type ≔ data [ zero. | suc. (_ : N) ]

` Symmetrically, here the motive supplies an index that V doesn't take, so the
` constructor outputs have one argument too few.
def V (n : N) : Type ≔ match n return _ ↦ N → Type [
| zero. ↦ data [ v0. : V n ]
| suc. m ↦ data [ v1. : V n ]
]
