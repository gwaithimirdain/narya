def N : Type ≔ data [ zero. | suc. (_ : N) ]

def Bool : Type ≔ data [ true. | false. ]

def W : Type ≔ data [ wrap. (x : N) | other. ]

def T : N → Type ≔ n ↦ match n [ zero. ↦ N | suc. _ ↦ Bool ]

axiom g : (n : N) → T n

axiom b : Bool
