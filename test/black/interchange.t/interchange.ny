{` -*- narya-prog-args: ("-proofgeneral" "-interchange") -*- `}

def ▹ (A :▹| AType) : BType ≔ data [ ▹. (_ :▹| A) ]
def ◃ (A :◃| AType) : BType ≔ data [ ◃. (_ :◃| A) ]

def ▸ (B :▸| BType) : CType ≔ data [ ▸. (_ :▸| B) ]
def ◂ (B :◂| BType) : CType ≔ data [ ◂. (_ :◂| B) ]

` The two generating 2-cells, alpha : ▹ ⇒ ◃ (over AType → BType) and beta : ▸ ⇒ ◂ (over
` BType → CType), each induce a function by relocking the field.
def alpha_map (A :▹| AType) (u : ▹ A) : ◃ A ≔ match u [ ▹. x ↦ ◃. x ]
def beta_map (B :▸| BType) (v : ▸ B) : ◂ B ≔ match v [ ▸. x ↦ ◂. x ]

` The functorial actions of ▸ and ◂ on functions between BType-types.
def ▸map (B C :▸| BType) (f :▸| B → C) : ▸ B → ▸ C ≔ [ ▸. x ↦ ▸. (f x) ]
def ◂map (B C :◂| BType) (f :◂| B → C) : ◂ B → ◂ C ≔ [ ◂. x ↦ ◂. (f x) ]

` The two composites around the interchange square: applying alpha_map first (under ▸,
` then relocking to ◂ via beta_map at ◃ A), versus applying beta_map first (at ▹ A, then
` applying ◂'s functorial action to alpha_map).
def route1 (A :▸▹| AType) (w : ▸ (▹ A)) : ◂ (◃ A) ≔
  beta_map (◃ A) (▸map (▹ A) (◃ A) (alpha_map A) w)

def route2 (A :▸▹| AType) (w : ▸ (▹ A)) : ◂ (◃ A) ≔
  ◂map (▹ A) (◃ A) (alpha_map A) (beta_map (▹ A) w)

` The interchange law: both routes agree, since the theory is locally posetal.
def interchange_ok (A :▸▹| AType) (w : ▸ (▹ A)) : Id (◂ (◃ A)) (route1 A w) (route2 A w) ≔
  match w [ ▸. x ↦ refl (◂. (alpha_map A x)) ]
