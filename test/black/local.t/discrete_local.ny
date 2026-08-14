option parametric ≔ arity 2, letter p, name rel Br
option modal ≔ discrete local

` In the discrete variant, ∇ is not tangible, so it can't appear in the
` argument of a datatype; but the rest of the normalization is the same.

def counit (A :△□| Type) (x :△□| A) : A ≔ x

def counit2 (A :△□△□| Type) (x :△□△□| A) : A ≔ x

def unit (A : Disc) (x :□△| A) : A ≔ x

def □△ (A : Disc) : Disc ≔ data [ t. (_ :□△| A) ]

def unit_inv (A : Disc) (x : A) : □△ A ≔ t. x

def epsilon (A : Disc) (x :□∇| A) : A ≔ x

def isos (A : Disc) (x :□△□∇| A) : A ≔ x

` The negative □ operator, using the sinister modality △.
def □′ (A :□| Type) : Disc ≔ codata [ (x :△| _) .unbox : A ]

def box (A :□| Type) (a :□| A) : □′ A ≔ [ .unbox ↦ a ]

def unbox (A :△□| Type) (u :△| □′ A) : A ≔ (u :△| _) .unbox

def unbox_box (A :△□| Type) (a :△□| A) : Br A (unbox A (box A a)) a
  ≔ rel a

` The negative ∇ operator, using the sinister modality □.
def ∇′ (A :△| Disc) : Type ≔ codata [ (x :□| _) .unnab : A ]

def nab (A :△| Disc) (a :△| A) : ∇′ A ≔ [ .unnab ↦ a ]

def unnab (A :□△| Disc) (u :□| ∇′ A) : A ≔ (u :□| _) .unnab

` (Disc is nonparametric in the discrete variant, so no Br-types there.)

def ∇″ (A :△| Disc) : Type ≔ sig ( (x :□| _) .unnab : A )

def nab_unnab (A :△| Disc) (u : ∇″ A) : ∇″ A ≔ (unnab ≔ (u :□| _) .unnab)

def nab_eta (A :△| Disc) (u : ∇″ A) : Br (∇″ A) (nab_unnab A u) u ≔ rel u

` The composite sinister modality △□ ⊣ ∇□.
def ∇□′ (A :∇□| Type) : Type ≔ codata [ (x :△□| _) .un : A ]

def mk (A :∇□| Type) (a :∇□| A) : ∇□′ A ≔ [ .un ↦ a ]

def unmk (A :△□∇□| Type) (u :△□| ∇□′ A) : A ≔ (u :△□| _) .un

def unmk_mk (A :△□∇□| Type) (a :△□∇□| A) : Br A (unmk A (mk A a)) a
  ≔ rel a
