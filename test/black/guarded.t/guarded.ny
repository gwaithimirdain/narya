{` -*- narya-prog-args: ("-proofgeneral" "-guarded") -*- `}

def ▹ (A :▹| Type) : Type ≔ data [ nxt. (_ :▹| A) ]

` The generating cell next : id ⇒ ▹ lets a plain value supply a ▹-locked field.
def eta (A : Type) (x : A) : ▹ A ≔ nxt. x

` It composes: id ⇒ ▹ ⇒ ▹▹ gives a plain value directly into a doubly-later position.
def eta2 (A : Type) (x : A) : ▹ (▹ A) ≔ nxt. (nxt. x)

` The negative □ operator, using the sinister modality △, exactly as in Coreflection.
def □ (A :□| Type) : Disc ≔ codata [ (x :△| _) .unbox : A ]

def box (A :□| Type) (a :□| A) : □ A ≔ [ .unbox ↦ a ]

def unbox (A :△□| Type) (u :△| □ A) : A ≔ (u :△| _) .unbox

` The isomorphism box.later ≅ box (□▹ ≅ □), in both directions: a □▹-locked value can supply a
` □-locked field...
def box_from_later (A :□▹| Type) (a :□▹| A) : □ A ≔ [ .unbox ↦ a ]

` ...and conversely, a □-locked value can supply a □▹-locked field.
def box_later_from_box (A :□| Type) (a :□| A) : □ (▹ A) ≔ [ .unbox ↦ nxt. a ]
