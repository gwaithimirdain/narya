{` -*- narya-prog-args: ("-proofgeneral" "-cospatial") -*- `}

` The counit of the coreflector ♭: a ♭-locked variable can be used directly.
def counit (A :♭| Type) (x :♭| A) : A ≔ x

` The reflector ʃ has no counit of its own, so it cannot be unlocked directly.

` A plain value can supply a ʃ-locked field (monad unit); ♭ has no unit of its own.
def shape : Type ≔ data [ shape. (_ :ʃ| Type) ]

def wsh (x : Type) : shape ≔ shape. x

` Idempotence of ʃ: a ʃʃ-locked variable can supply a ʃ-locked field, and vice versa.
def ss : Type ≔ data [ ss. (_ :ʃ| Type) ]

def wss (x :ʃʃ| Type) : ss ≔ ss. x

def ss2 : Type ≔ data [ ss2. (_ :ʃʃ| Type) ]

def wss2 (x :ʃ| Type) : ss2 ≔ ss2. x

` Idempotence of ♭: dually, a ♭-locked variable can supply a ♭♭-locked field, and vice versa.
def ff : Type ≔ data [ ff. (_ :♭♭| Type) ]

def wff (x :♭| Type) : ff ≔ ff. x

def ff2 : Type ≔ data [ ff2. (_ :♭| Type) ]

def wff2 (x :♭♭| Type) : ff2 ≔ ff2. x

` The isomorphism ʃ♭ ≅ ♭: each can supply a field locked by the other.
def sf : Type ≔ data [ sf. (_ :♭| Type) ]

def wsf (x :ʃ♭| Type) : sf ≔ sf. x

def sf2 : Type ≔ data [ sf2. (_ :ʃ♭| Type) ]

def wsf2 (x :♭| Type) : sf2 ≔ sf2. x

` The isomorphism ♭ʃ ≅ ʃ: likewise.
def fs : Type ≔ data [ fs. (_ :ʃ| Type) ]

def wfs (x :♭ʃ| Type) : fs ≔ fs. x

def fs2 : Type ≔ data [ fs2. (_ :♭ʃ| Type) ]

def wfs2 (x :ʃ| Type) : fs2 ≔ fs2. x

` The induced adjunction ʃ ⊣ ♭: unit id ⇒ ♭ʃ and counit ʃ♭ ⇒ id.
def adjunit : Type ≔ data [ au. (_ :♭ʃ| Type) ]

def wau (x : Type) : adjunit ≔ au. x

def adjcounit (A :ʃ♭| Type) (x :ʃ♭| A) : A ≔ x

` The negative operator dual to ♭, using the sinister modality ʃ (left adjoint to ♭).
def Neg (A :♭| Type) : Type ≔ codata [ (x :ʃ| _) .un : A ]

def mk (A :♭| Type) (a :♭| A) : Neg A ≔ [ .un ↦ a ]

def unmk (A :ʃ♭| Type) (u :ʃ| Neg A) : A ≔ (u :ʃ| _) .un

` unmk (mk a) reduces to a, with the (unique) counit key applied.
def unmk_mk (A :ʃ♭| Type) (a :ʃ♭| A) : Id A (unmk A (mk A a)) a ≔ refl a

` ♭ has no unit of its own: a plain value cannot supply a bare ♭-locked field.
def bad1 : Type ≔ data [ bad1. (_ :♭| Type) ]

` def wbad1 (x : Type) : bad1 ≔ bad1. x

` The reflector ʃ has no counit of its own.
` def bad2 (A :ʃ| Type) (x :ʃ| A) : A ≔ x

` The unit and counit only go in the induced direction ʃ ⊣ ♭, not the other way around.
def bad3 : Type ≔ data [ bad3. (_ :ʃ♭| Type) ]

` def wbad3 (x : Type) : bad3 ≔ bad3. x
` def bad4 (A :♭ʃ| Type) (x :♭ʃ| A) : A ≔ x

` And there are no cells crossing directly between ʃ and ♭ in the "wrong" direction.
` def bad5 (A :ʃ| Type) (x :♭| A) : A ≔ x
