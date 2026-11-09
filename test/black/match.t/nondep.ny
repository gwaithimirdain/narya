def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
def Vec (A : Type) : ℕ → Type ≔ data [ nil. : Vec A zero. | cons. (n:ℕ) (_:A) (_:Vec A n) : Vec A (suc. n) ]
{` A match with "return _" doesn't refine the goal, so this fails `}
def idvec (A : Type) (n : ℕ) (v : Vec A n) : Vec A n ≔ match v return _ [ nil. ↦ nil. | cons. m x xs ↦ cons. m x xs ]
