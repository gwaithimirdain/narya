{` -*- narya-prog-args: ("-proofgeneral" "-dtt") -*- `}

` The Dtt mode theory has two modes, Disc and Type, and three generating
` modalities △ : Disc → Type, □ : Type → Disc, ◇ : Type → Disc, with an adjoint
` triple ◇ ⊣ △ ⊣ □.  The left adjoints ◇ and △ are sinister, so they can
` parametrize modal fields.

` A Type-record with a ◇-modal field (◇ ⊣ △).  Its type lives at Disc, checked
` in a context locked by the right adjoint △; the projection lands at Disc.
def C : Type ≔ codata [ (x :◇| _) .fld : Disc ]

axiom z : C

` A Disc-record with a △-modal field (△ ⊣ □).  Its type lives at Type, checked
` in a context locked by the right adjoint □; the projection lands at Type.
def K : Disc ≔ codata [ (x :△| _) .obj : Type ]

axiom k : K

` A △□-annotated variable (△□ is the nonparametric coreflector "♭") can be used
` unlocked, via the counit △□ ⇒ id.
def counit (A :△ □| Type) : Type ≔ A
