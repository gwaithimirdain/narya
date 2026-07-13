{` -*- narya-prog-args: ("-proofgeneral" "-composed-functors") -*- `}

` The modal operators associated to ○, ▱, and their composite ▱○.

def ○ (X :○| AType) : BType ≔ data [ circ. (_ :○| X) ]

def ▱ (Y :▱| BType) : CType ≔ data [ par. (_ :▱| Y) ]

def ▱○ (X :▱○| AType) : CType ≔ data [ parcirc. (_ :▱○| X) ]

{` We can define one direction without windows. `}
def colax (X :▱○| AType) (u : ▱○ X) : ▱ (○ X) ≔ match u [
| parcirc. x ↦ par. (circ. x)]

` The composite of the modal operators ○ and ▱ is the modal operator of the
` composite modality, up to isomorphism.  The forward map requires matching
` under the window modality ▱ to reach inside the datatype ○.

def lax (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
| par. y ↦ match (y :▱| _) [ circ. x ↦ parcirc. x ]]

{` We can also give the type explicitly `}
def lax′ (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
| par. y ↦ match (y :▱| ○ X) [ circ. x ↦ parcirc. x ]]

{` Or, in fact, leave off the window annotation, since [y] is a variable whose annotation is known `}
def lax″ (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
| par. y ↦ match y [ circ. x ↦ parcirc. x ]]

def lax∘colax (X :▱○| AType) (u : ▱○ X) : Id (▱○ X) (lax X (colax X u)) u
  ≔ match u [ parcirc. x ↦ refl (parcirc. x) ]

def colax∘lax (X :▱○| AType) (u : ▱ (○ X))
  : Id (▱ (○ X)) (colax X (lax X u)) u
  ≔ match u [
| par. y ↦ match (y :▱| _) [ circ. x ↦ refl (par. (circ. x)) ]]
