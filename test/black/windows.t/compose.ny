{` -*- narya-prog-args: ("-proofgeneral" "-composed-functors") -*- `}

` The modal operators associated to F, G, and their composite G∘F.

def F (X :F| AType) : BType ≔ data [ f. (_ :F| X) ]

def G (Y :G| BType) : CType ≔ data [ g. (_ :G| Y) ]

def GF (X :G F| AType) : CType ≔ data [ gf. (_ :G F| X) ]

` The composite of the modal operators F and G is the modal operator of the
` composite modality, up to isomorphism.  The forward map requires matching
` under the window modality G to reach inside the datatype F.

def fwd (X :G F| AType) (u : G (F X)) : GF X ≔ match u [
| g. y ↦ match (y :G| _) [ f. x ↦ gf. x ]]

def bwd (X :G F| AType) (u : GF X) : G (F X) ≔ match u [ gf. x ↦ g. (f. x) ]

def fwd∘bwd (X :G F| AType) (u : GF X) : Id (GF X) (fwd X (bwd X u)) u ≔ match u [
| gf. x ↦ refl (gf. x)]

def bwd∘fwd (X :G F| AType) (u : G (F X)) : Id (G (F X)) (bwd X (fwd X u)) u
  ≔ match u [ g. y ↦ match (y :G| _) [ f. x ↦ refl (g. (f. x)) ]]
