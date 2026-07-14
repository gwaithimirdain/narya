{` -*- narya-prog-args: ("-proofgeneral" "-cospatial") -*- `}

` The counit of the coreflector ♭: a ♭-locked variable can be used directly.
def counit (A :♭| Type) (x :♭| A) : A ≔ x

` The reflector ♯ has no counit of its own, so it cannot be unlocked directly.

` A plain value can supply a ♯-locked field (monad unit); ♭ has no unit of its own.
def sharp : Type ≔ data [ sharp. (_ :♯| Type) ]

def wsh (x : Type) : sharp ≔ sharp. x

` Idempotence of ♯: a ♯♯-locked variable can supply a ♯-locked field, and vice versa.
def ss : Type ≔ data [ ss. (_ :♯| Type) ]

def wss (x :♯♯| Type) : ss ≔ ss. x

def ss2 : Type ≔ data [ ss2. (_ :♯♯| Type) ]

def wss2 (x :♯| Type) : ss2 ≔ ss2. x

` Idempotence of ♭: dually, a ♭-locked variable can supply a ♭♭-locked field, and vice versa.
def ff : Type ≔ data [ ff. (_ :♭♭| Type) ]

def wff (x :♭| Type) : ff ≔ ff. x

def ff2 : Type ≔ data [ ff2. (_ :♭| Type) ]

def wff2 (x :♭♭| Type) : ff2 ≔ ff2. x

` The isomorphism ♯♭ ≅ ♭: each can supply a field locked by the other.
def sf : Type ≔ data [ sf. (_ :♭| Type) ]

def wsf (x :♯♭| Type) : sf ≔ sf. x

def sf2 : Type ≔ data [ sf2. (_ :♯♭| Type) ]

def wsf2 (x :♭| Type) : sf2 ≔ sf2. x

` The isomorphism ♭♯ ≅ ♯: likewise.
def fs : Type ≔ data [ fs. (_ :♯| Type) ]

def wfs (x :♭♯| Type) : fs ≔ fs. x

def fs2 : Type ≔ data [ fs2. (_ :♭♯| Type) ]

def wfs2 (x :♯| Type) : fs2 ≔ fs2. x

` The induced adjunction ♯ ⊣ ♭: unit id ⇒ ♭♯ and counit ♯♭ ⇒ id.
def adjunit : Type ≔ data [ au. (_ :♭♯| Type) ]

def wau (x : Type) : adjunit ≔ au. x

def adjcounit (A :♯♭| Type) (x :♯♭| A) : A ≔ x

` The negative operator dual to ♭, using the sinister modality ♯ (left adjoint to ♭).
def Neg (A :♭| Type) : Type ≔ codata [ (x :♯| _) .un : A ]

def mk (A :♭| Type) (a :♭| A) : Neg A ≔ [ .un ↦ a ]

def unmk (A :♯♭| Type) (u :♯| Neg A) : A ≔ (u :♯| _) .un

` unmk (mk a) reduces to a, with the (unique) counit key applied.
def unmk_mk (A :♯♭| Type) (a :♯♭| A) : Id A (unmk A (mk A a)) a ≔ refl a

` ♭ has no unit of its own: a plain value cannot supply a bare ♭-locked field.
def bad1 : Type ≔ data [ bad1. (_ :♭| Type) ]

` def wbad1 (x : Type) : bad1 ≔ bad1. x

` The reflector ♯ has no counit of its own.
` def bad2 (A :♯| Type) (x :♯| A) : A ≔ x

` The unit and counit only go in the induced direction ♯ ⊣ ♭, not the other way around.
def bad3 : Type ≔ data [ bad3. (_ :♯♭| Type) ]

` def wbad3 (x : Type) : bad3 ≔ bad3. x
` def bad4 (A :♭♯| Type) (x :♭♯| A) : A ≔ x

` And there are no cells crossing directly between ♯ and ♭ in the "wrong" direction.
` def bad5 (A :♯| Type) (x :♭| A) : A ≔ x
