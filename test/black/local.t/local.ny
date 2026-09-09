{` -*- narya-prog-args: ("-proofgeneral" "-local") -*- `}

` The counit of △ ⊣ □: a △□-locked variable can be used directly.
def counit (A :△□| Type) (x :△□| A) : A ≔ x

` The doubled counit △□△□ ⇒ 1 is unique.
def counit2 (A :△□△□| Type) (x :△□△□| A) : A ≔ x

` The invertible unit of △ ⊣ □, in both directions.
def unit (A : Disc) (x :□△| A) : A ≔ x

def □△ (A : Disc) : Disc ≔ data [ t. (_ :□△| A) ]

def unit_inv (A : Disc) (x : A) : □△ A ≔ t. x

` The invertible counit of □ ⊣ ∇, in both directions.
def epsilon (A : Disc) (x :□∇| A) : A ≔ x

def □∇ (A : Disc) : Disc ≔ data [ e. (_ :□∇| A) ]

def epsilon_inv (A : Disc) (x : A) : □∇ A ≔ e. x

` A longer normalization □△□∇ ≅ 1.
def isos (A : Disc) (x :□△□∇| A) : A ≔ x

` The unit of □ ⊣ ∇ is not invertible, but 1 ⇒ ∇□ is unique.
def ∇□ (A : Type) : Type ≔ data [ c. (_ :∇□| A) ]

def eta (A : Type) (x : A) : ∇□ A ≔ c. x

` So is its nested version 1 ⇒ ∇□△□, a unit under the counit.
def ∇□△□ (A : Type) : Type ≔ data [ c2. (_ :∇□△□| A) ]

def eta2 (A : Type) (x : A) : ∇□△□ A ≔ c2. x

` The induced cell △ ⇒ ∇, and the composite △□ ⇒ ∇□.
def trinab (X :△| Disc) : Type ≔ data [ tn. (_ :∇| X) ]

def tribox_nabbox (X :△□| Type) : Type ≔ data [ tb. (_ :∇□| X) ]

` Combined with normalization: △□△ ≅ △ ⇒ ∇.
def trinab2 (X :△□△| Disc) : Type ≔ data [ tn2. (_ :∇| X) ]

` The negative □ operator, using the sinister modality △.
def □′ (A :□| Type) : Disc ≔ codata [ (x :△| _) .unbox : A ]

def box (A :□| Type) (a :□| A) : □′ A ≔ [ .unbox ↦ a ]

def unbox (A :△□| Type) (u :△| □′ A) : A ≔ (u :△| _) .unbox

` unbox (box a) reduces to a, with the (unique) counit key applied.
def unbox_box (A :△□| Type) (a :△□| A) : Id A (unbox A (box A a)) a
  ≔ refl a

` The negative ∇ operator, using the sinister modality □.
def ∇′ (A :△| Disc) : Type ≔ codata [ (x :□| _) .unnab : A ]

def nab (A :△| Disc) (a :△| A) : ∇′ A ≔ [ .unnab ↦ a ]

def unnab (A :□△| Disc) (u :□| ∇′ A) : A ≔ (u :□| _) .unnab

def unnab_nab (A :□△| Disc) (a :□△| A) : Id A (unnab A (nab A a)) a
  ≔ refl a

` The record version has an η-rule, tested by applying a key and comparing
` the resulting cells.
def ∇″ (A :△| Disc) : Type ≔ sig ( (x :□| _) .unnab : A )

def nab_unnab (A :△| Disc) (u : ∇″ A) : ∇″ A ≔ (unnab ≔ (u :□| _) .unnab)

def nab_eta (A :△| Disc) (u : ∇″ A) : Id (∇″ A) (nab_unnab A u) u ≔ refl u

` The composite sinister modality △□ ⊣ ∇□ also supports a negative operator.
def ∇□′ (A :∇□| Type) : Type ≔ codata [ (x :△□| _) .un : A ]

def mk (A :∇□| Type) (a :∇□| A) : ∇□′ A ≔ [ .un ↦ a ]

def unmk (A :△□∇□| Type) (u :△□| ∇□′ A) : A ≔ (u :△□| _) .un

def unmk_mk (A :△□∇□| Type) (a :△□∇□| A) : Id A (unmk A (mk A a)) a
  ≔ refl a
