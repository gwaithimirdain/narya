{` -*- narya-prog-args: ("-proofgeneral" "-guarded") -*- `}

def ▸ (A :▸| Timed) : Timed ≔ data [ ▸. (_ :▸| A) ]

` The generating cell next : id ⇒ ▸ lets a plain value supply a ▸-locked field.
def next (A : Timed) (x : A) : ▸ A ≔ ▸. x

` It composes: id ⇒ ▸ ⇒ ▸▸ gives a plain value directly into a doubly-later position.
def next2 (A : Timed) (x : A) : ▸ (▸ A) ≔ ▸. (▸. x)

` The negative □ operator, using the sinister modality △, exactly as in Coreflection.
def □ (A :□| Timed) : Type ≔ codata [ (_ :△| _) .□ : A ]

def box (A :□| Timed) (a :□| A) : □ A ≔ [ .□ ↦ a ]

def unbox (A :△□| Timed) (u :△| □ A) : A ≔ (u :△| _) .□

` The isomorphism box.later ≅ box (□▸ ≅ □), in both directions: a □▸-locked value can supply a
` □-locked field...
def box_from_later (A :□▸| Timed) (a :□▸| A) : □ A ≔ [ .□ ↦ a ]

` ...and conversely, a □-locked value can supply a □▸-locked field.
def box_later_from_box (A :□| Timed) (a :□| A) : □ (▸ A) ≔ [
| .□ ↦ ▸. a]
