{` -*- narya-prog-args: ("-proofgeneral" "-gwpt") -*- `}

` The counit of △ ⊣ □: a △□-locked variable can be used directly.
def counit (A :△□| Type) (x :△□| A) : A ≔ x

` The monad □△ on Disc as a modal datatype, with its unit.
def □△ (A : Disc) : Disc ≔ data [ □△. (_ :□△| A) ]

def eta (A : Disc) (x : A) : □△ A ≔ □△. x

` The doubled counit △□△□ ⇒ 1 is unique.
def counit2 (A :△□△□| Type) (x :△□△□| A) : A ≔ x

` The invertible counit of ◇ ⊣ ∇, in both directions.
def epsilon (A : Disc) (x :◇∇| A) : A ≔ x

def ◇∇ (A : Disc) : Disc ≔ data [ ◇∇. (_ :◇∇| A) ]

def epsilon_inv (A : Disc) (x : A) : ◇∇ A ≔ ◇∇. x

` The other two isomorphisms ◇△ ≅ 1 and □∇ ≅ 1.
def theta (A : Disc) (x :◇△| A) : A ≔ x

def phi (A : Disc) (x :□∇| A) : A ≔ x

` A longer normalization ◇△□∇ ≅ 1, composed with the unit 1 ⇒ □△.
def isos (A : Disc) (x :◇△□∇| A) : □△ A ≔ □△. x

` The unit of ◇ ⊣ ∇ is not invertible, but 1 ⇒ ∇◇ is unique.
def ∇◇ (A : Type) : Type ≔ data [ ∇◇. (_ :∇◇| A) ]

def eta' (A : Type) (x : A) : ∇◇ A ≔ ∇◇. x

` So is its nested version 1 ⇒ ∇□△◇: a unit η under the cap η'.
def ∇□△◇ (A : Type) : Type ≔ data [ ∇□△◇. (_ :∇□△◇| A) ]

def eta'2 (A : Type) (x : A) : ∇□△◇ A ≔ ∇□△◇. x

` The induced cells □ ⇒ ◇ and △ ⇒ ∇.
def boxdia (X :□| Type) : Disc ≔ data [ ◇. (_ :◇| X) ]

def trinab (X :△| Disc) : Type ≔ data [ ∇. (_ :∇| X) ]

` Combined with normalization: △◇∇ ≅ △ ⇒ ∇.
def trinab2 (X :△◇∇| Disc) : Type ≔ data [ ∇. (_ :∇| X) ]

` The negative □ operator, using the sinister modality △.
def □ (A :□| Type) : Disc ≔ codata [ (_ :△| _) .□ : A ]

def box (A :□| Type) (a :□| A) : □ A ≔ [ .□ ↦ a ]

def unbox (A :△□| Type) (u :△| □ A) : A ≔ (u :△| _) .□

` unbox (box a) reduces to a, with the (unique) counit key applied.
def unbox_box (A :△□| Type) (a :△□| A) : Id A (unbox A (box A a)) a
  ≔ refl a

` The negative ∇ operator, using the sinister modality ◇.
def ∇ (A :∇| Disc) : Type ≔ codata [ (_ :◇| _) .∇ : A ]

def nab (A :∇| Disc) (a :∇| A) : ∇ A ≔ [ .∇ ↦ a ]

def unnab (A :◇∇| Disc) (u :◇| ∇ A) : A ≔ (u :◇| _) .∇

def unnab_nab (A :◇∇| Disc) (a :◇∇| A) : Id A (unnab A (nab A a)) a
  ≔ refl a

` The record version has an η-rule, tested by applying the unit η' as a key and
` comparing the resulting cells by their pairings (in which the invertible
` counit ε' can cancel its formal inverse, forming droppable closed loops).
def ∇′ (A :∇| Disc) : Type ≔ sig ( (_ :◇| _) .∇ : A )

def nab_unnab (A :∇| Disc) (u : ∇′ A) : ∇′ A ≔ (∇ ≔ (u :◇| _) .∇)

def nab_eta (A :∇| Disc) (u : ∇′ A) : Id (∇′ A) (nab_unnab A u) u ≔ refl u

` The composite sinister modality △◇ ⊣ ∇□ also supports a negative operator.
def ∇□ (A :∇□| Type) : Type ≔ codata [ (_ :△◇| _) .∇□ : A ]

def mk (A :∇□| Type) (a :∇□| A) : ∇□ A ≔ [ .∇□ ↦ a ]

def unmk (A :△◇∇□| Type) (u :△◇| ∇□ A) : A ≔ (u :△◇| _) .∇□

def unmk_mk (A :△◇∇□| Type) (a :△◇∇□| A) : Id A (unmk A (mk A a)) a
  ≔ refl a
