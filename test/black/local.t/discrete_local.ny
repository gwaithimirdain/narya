{` -*- narya-prog-args: ("-proofgeneral" "-discrete-local" "-parametric") -*- `}

` In the discrete variant, ∇ is not tangible, so it can't appear in the
` argument of a datatype; but the rest of the normalization is the same.

def counit (A :△□| Type) (x :△□| A) : A ≔ x

def counit2 (A :△□△□| Type) (x :△□△□| A) : A ≔ x

def unit (A : Disc) (x :□△| A) : A ≔ x

def □△ (A : Disc) : Disc ≔ data [ □△. (_ :□△| A) ]

def unit_inv (A : Disc) (x : A) : □△ A ≔ □△. x

def epsilon (A : Disc) (x :□∇| A) : A ≔ x

def isos (A : Disc) (x :□△□∇| A) : A ≔ x

` The negative □ operator, using the sinister modality △.
def □ (A :□| Type) : Disc ≔ codata [ (_ :△| _) .□ : A ]

def box (A :□| Type) (a :□| A) : □ A ≔ [ .□ ↦ a ]

def unbox (A :△□| Type) (u :△| □ A) : A ≔ (u :△| _) .□

def unbox_box (A :△□| Type) (a :△□| A) : Id A (unbox A (box A a)) a
  ≔ refl a

` The negative ∇ operator, using the sinister modality □.
def ∇ (A :△| Disc) : Type ≔ codata [ (_ :□| _) .∇ : A ]

def nab (A :△| Disc) (a :△| A) : ∇ A ≔ [ .∇ ↦ a ]

def unnab (A :□△| Disc) (u :□| ∇ A) : A ≔ (u :□| _) .∇

` (Disc is nonparametric in the discrete variant, so no Id-types there.)

def ∇′ (A :△| Disc) : Type ≔ sig ( (_ :□| _) .∇ : A )

def nab_unnab (A :△| Disc) (u : ∇′ A) : ∇′ A ≔ (∇ ≔ (u :□| _) .∇)

def nab_eta (A :△| Disc) (u : ∇′ A) : Id (∇′ A) (nab_unnab A u) u ≔ refl u

` The composite sinister modality △□ ⊣ ∇□.
def ∇□ (A :∇□| Type) : Type ≔ codata [ (_ :△□| _) .∇□ : A ]

def mk (A :∇□| Type) (a :∇□| A) : ∇□ A ≔ [ .∇□ ↦ a ]

def unmk (A :△□∇□| Type) (u :△□| ∇□ A) : A ≔ (u :△□| _) .∇□

def unmk_mk (A :△□∇□| Type) (a :△□∇□| A) : Id A (unmk A (mk A a)) a
  ≔ refl a
