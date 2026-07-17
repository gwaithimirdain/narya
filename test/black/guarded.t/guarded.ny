{` -*- narya-prog-args: ("-proofgeneral" "-guarded") -*- `}

def ▹ (A :▹| Timed) : Timed ≔ data [ nxt. (_ :▹| A) ]

` The generating cell next : id ⇒ ▹ lets a plain value supply a ▹-locked field.
def eta (A : Timed) (x : A) : ▹ A ≔ nxt. x

` It composes: id ⇒ ▹ ⇒ ▹▹ gives a plain value directly into a doubly-later position.
def eta2 (A : Timed) (x : A) : ▹ (▹ A) ≔ nxt. (nxt. x)

` The negative □ operator, using the sinister modality △, exactly as in Coreflection.
def □ (A :□| Timed) : Type ≔ codata [ (x :△| _) .unbox : A ]

def box (A :□| Timed) (a :□| A) : □ A ≔ [ .unbox ↦ a ]

def unbox (A :△□| Timed) (u :△| □ A) : A ≔ (u :△| _) .unbox

` The isomorphism box.later ≅ box (□▹ ≅ □), in both directions: a □▹-locked value can supply a
` □-locked field...
def box_from_later (A :□▹| Timed) (a :□▹| A) : □ A ≔ [ .unbox ↦ a ]

` ...and conversely, a □-locked value can supply a □▹-locked field.
def box_later_from_box (A :□| Timed) (a :□| A) : □ (▹ A) ≔ [ .unbox ↦ nxt. a ]
