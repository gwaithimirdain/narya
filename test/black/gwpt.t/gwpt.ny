{` -*- narya-prog-args: ("-proofgeneral" "-gwpt") -*- `}

` The counit of △ ⊣ □: a △□-locked variable can be used directly.
def counit (A : △□ | Type) (x : △□ | A) : A ≔ x

` The monad □△ on Disc as a modal datatype, with its unit.
def T (A : Disc) : Disc ≔ data [ t. (_ : □△ | A) ]

def eta (A : Disc) (x : A) : T A ≔ t. x

` The doubled counit △□△□ ⇒ 1 is unique.
def counit2 (A : △□△□ | Type) (x : △□△□ | A) : A ≔ x

` The invertible counit of ◇ ⊣ ∇, in both directions.
def epsilon (A : Disc) (x : ◇∇ | A) : A ≔ x

def E (A : Disc) : Disc ≔ data [ e. (_ : ◇∇ | A) ]

def epsilon_inv (A : Disc) (x : A) : E A ≔ e. x

` The other two isomorphisms ◇△ ≅ 1 and □∇ ≅ 1.
def theta (A : Disc) (x : ◇△ | A) : A ≔ x

def phi (A : Disc) (x : □∇ | A) : A ≔ x

` A longer normalization ◇△□∇ ≅ 1, composed with the unit 1 ⇒ □△.
def isos (A : Disc) (x : ◇△□∇ | A) : T A ≔ t. x

` The unit of ◇ ⊣ ∇ is not invertible, but 1 ⇒ ∇◇ is unique.
def C (A : Type) : Type ≔ data [ c. (_ : ∇◇ | A) ]

def eta' (A : Type) (x : A) : C A ≔ c. x

` So is its nested version 1 ⇒ ∇□△◇: a unit η under the cap η'.
def C2 (A : Type) : Type ≔ data [ c2. (_ : ∇□△◇ | A) ]

def eta'2 (A : Type) (x : A) : C2 A ≔ c2. x

` The induced cells □ ⇒ ◇ and △ ⇒ ∇.
def boxdia (X : □ | Type) : Disc ≔ data [ bd. (_ : ◇ | X) ]

def trinab (X : △ | Disc) : Type ≔ data [ tn. (_ : ∇ | X) ]

` Combined with normalization: △◇∇ ≅ △ ⇒ ∇.
def trinab2 (X : △◇∇ | Disc) : Type ≔ data [ tn2. (_ : ∇ | X) ]

` The negative □ operator, using the sinister modality △.
def □ (A :□| Type) : Disc ≔ codata [ (x :△| _) .unbox : A ]

def box (A :□| Type) (a :□| A) : □ A ≔ [ .unbox ↦ a ]

def unbox (A :△□| Type) (u :△| □ A) : A ≔ (u :△| _) .unbox

` unbox (box a) reduces to a, with the (unique) counit key applied.
def unbox_box (A :△□| Type) (a :△□| A) : Id A (unbox A (box A a)) a ≔ refl a

` The negative ∇ operator, using the sinister modality ◇.
def ∇′ (A :∇| Disc) : Type ≔ codata [ (x :◇| _) .unnab : A ]

def nab (A :∇| Disc) (a :∇| A) : ∇′ A ≔ [ .unnab ↦ a ]

def unnab (A :◇∇| Disc) (u :◇| ∇′ A) : A ≔ (u :◇| _) .unnab

def unnab_nab (A :◇∇| Disc) (a :◇∇| A) : Id A (unnab A (nab A a)) a ≔ refl a

` The record version has an η-rule, tested by applying the unit η' as a key and
` comparing the resulting cells by their pairings (in which the invertible
` counit ε' can cancel its formal inverse, forming droppable closed loops).
def ∇″ (A :∇| Disc) : Type ≔ sig ( (x :◇| _) .unnab : A )

def nab_unnab (A :∇| Disc) (u : ∇″ A) : ∇″ A ≔ (unnab ≔ (u :◇| _) .unnab)

def nab_eta (A :∇| Disc) (u : ∇″ A) : Id (∇″ A) (nab_unnab A u) u ≔ refl u

` The composite sinister modality △◇ ⊣ ∇□ also supports a negative operator.
def NB (A :∇□| Type) : Type ≔ codata [ (x :△◇| _) .un : A ]

def mk (A :∇□| Type) (a :∇□| A) : NB A ≔ [ .un ↦ a ]

def unmk (A :△◇∇□| Type) (u :△◇| NB A) : A ≔ (u :△◇| _) .un

def unmk_mk (A :△◇∇□| Type) (a :△◇∇□| A) : Id A (unmk A (mk A a)) a ≔ refl a
