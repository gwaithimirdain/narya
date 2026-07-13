{` -*- narya-prog-args: ("-proofgeneral" "-adjunction") -*- `}

` The counit: a △□-locked variable can be used directly.
def counit (A : △□ | Type) (x : △□ | A) : A ≔ x

` The doubled counit △□△□ ⇒ 1 is also unique (its two factorizations through △□ agree).
def counit2 (A : △□△□ | Type) (x : △□△□ | A) : A ≔ x

` The monad □△ on Disc, as a modal datatype, and its square.
def T (A : Disc) : Disc ≔ data [ t. (_ : □△ | A) ]

def T2 (A : Disc) : Disc ≔ data [ t2. (_ : □△□△ | A) ]

` The unit: a plain value can supply a □△-locked argument.
def eta (A : Disc) (x : A) : T A ≔ t. x

` The doubled unit 1 ⇒ □△□△ is also unique.
def eta2 (A : Disc) (x : A) : T2 A ≔ t2. x

` The multiplication: the 2-cell □△□△ ⇒ □△ is unique.
def mu (A : Disc) (x : □△□△ | A) : T A ≔ t. x

` The comonad △□ on Type, as a modal datatype.
def S (A : △□ | Type) : Type ≔ data [ s. (_ : △□ | A) ]

` The negative □ operator, using the sinister modality △.
def □ (A :□| Type) : Disc ≔ codata [ (x :△| _) .unbox : A ]

def box (A :□| Type) (a :□| A) : □ A ≔ [ .unbox ↦ a ]

def unbox (A :△□| Type) (u :△| □ A) : A ≔ (u :△| _) .unbox

` unbox (box a) reduces to a, with the (unique) counit key applied; the two
` derivations of that key are equal since they induce the same pairing.
def unbox_box (A :△□| Type) (a :△□| A) : Id A (unbox A (box A a)) a ≔ refl a

` The record version has an η-rule, which is tested by applying the unit as a
` key and comparing the resulting cells by their pairings.
def □′ (A :□| Type) : Disc ≔ sig ( (x :△| _) .unbox : A )

def box_unbox (A :□| Type) (u : □′ A) : □′ A ≔ (unbox ≔ (u :△| _) .unbox)

def box_eta (A :□| Type) (u : □′ A) : Id (□′ A) (box_unbox A u) u ≔ refl u
