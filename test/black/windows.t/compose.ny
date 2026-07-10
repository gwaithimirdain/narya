{` -*- narya-prog-args: ("-proofgeneral" "-composed-functors") -*- `}

` The modal operators associated to F, G, and their composite G∘F.

def F (X :○| AType) : BType ≔ data [ f. (_ :○| X) ]

def G (Y :▱| BType) : CType ≔ data [ g. (_ :▱| Y) ]

def GF (X :▱○| AType) : CType ≔ data [ gf. (_ :▱○| X) ]

` The composite of the modal operators F and G is the modal operator of the
` composite modality, up to isomorphism.  The forward map requires matching
` under the window modality G to reach inside the datatype F.

def fwd (X :▱○| AType) (u : G (F X)) : GF X ≔ match u [
| g. y ↦ match (y :▱| _) [ f. x ↦ gf. x ]]

def bwd (X :▱○| AType) (u : GF X) : G (F X) ≔ match u [ gf. x ↦ g. (f. x) ]

def fwd∘bwd (X :▱○| AType) (u : GF X) : Id (GF X) (fwd X (bwd X u)) u ≔ match u [
| gf. x ↦ refl (gf. x)]

def bwd∘fwd (X :▱○| AType) (u : G (F X)) : Id (G (F X)) (bwd X (fwd X u)) u
  ≔ match u [ g. y ↦ match (y :▱| _) [ f. x ↦ refl (g. (f. x)) ]]
