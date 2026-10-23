{` -*- narya-prog-args: ("-proofgeneral" "-composable-functors") -*- `}

` The modal operators associated to ○, ▱, and their composite ▱○.

def ○ (X :○| AType) : BType ≔ data [ ○. (_ :○| X) ]

def ▱ (Y :▱| BType) : CType ≔ data [ ▱. (_ :▱| Y) ]

def ▱○ (X :▱○| AType) : CType ≔ data [ ▱○. (_ :▱○| X) ]

{` We can define one direction without windows. `}
def colax (X :▱○| AType) (u : ▱○ X) : ▱ (○ X) ≔ match u [
| ▱○. x ↦ ▱. (○. x)]

` The composite of the modal operators ○ and ▱ is the modal operator of the
` composite modality, up to isomorphism.  The forward map requires matching
` under the window modality ▱ to reach inside the datatype ○.

def lax (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
| ▱. y ↦ match (y :▱| _) [ ○. x ↦ ▱○. x ]]

{` We can also give the type explicitly `}
def lax′ (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
| ▱. y ↦ match (y :▱| ○ X) [ ○. x ↦ ▱○. x ]]

{` Or, in fact, leave off the window annotation, since [y] is a variable whose annotation is known `}
def lax″ (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
| ▱. y ↦ match y [ ○. x ↦ ▱○. x ]]

def lax∘colax (X :▱○| AType) (u : ▱○ X) : Id (▱○ X) (lax X (colax X u)) u
  ≔ match u [ ▱○. x ↦ refl (▱○. x) ]

def colax∘lax (X :▱○| AType) (u : ▱ (○ X))
  : Id (▱ (○ X)) (colax X (lax X u)) u
  ≔ match u [
| ▱. y ↦ match (y :▱| _) [ ○. x ↦ refl (▱. (○. x)) ]]
