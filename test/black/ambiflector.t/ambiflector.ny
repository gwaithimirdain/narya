{` -*- narya-prog-args: ("-proofgeneral" "-ambiflector") -*- `}

` The counit: a ♮-locked variable can be used directly.
def counit (A :♮| Type) (x :♮| A) : A ≔ x

` The unit: a plain value can supply a ♮-locked field.
def sharp : Type ≔ data [ sharp. (_ :♮| Type) ]

def wsh (x : Type) : sharp ≔ sharp. x

` Idempotence up to isomorphism: a ♮♮-locked variable can supply a ♮-locked field, and vice versa.
def ss : Type ≔ data [ ss. (_ :♮| Type) ]

def wss (x :♮♮| Type) : ss ≔ ss. x

def ss2 : Type ≔ data [ ss2. (_ :♮♮| Type) ]

def wss2 (x :♮| Type) : ss2 ≔ ss2. x

` The idempotence collapses arbitrarily long chains, not just doubled ones.
def ss3 : Type ≔ data [ ss3. (_ :♮♮♮| Type) ]

def wss3 (x :♮| Type) : ss3 ≔ ss3. x

def ss4 : Type ≔ data [ ss4. (_ :♮| Type) ]

def wss4 (x :♮♮♮♮| Type) : ss4 ≔ ss4. x

` Unlike an ordinary reflector or coreflector alone, ♮ having both a unit and a counit means
` every pair of ♮-words (id or ♮, the only two normal forms) has a key in both directions, so
` there is no analogue of the usual "missing key" test here.

` ♮ is adjoint to itself (unit id ⇒ ♮∘♮ via unit-then-comult, counit ♮∘♮ ⇒ id via mult-then-counit),
` so it is sinister and can parametrize a modal (negative) field.
def Neg (A :♮| Type) : Type ≔ codata [ (x :♮| _) .un : A ]

def mk (A :♮| Type) (a :♮| A) : Neg A ≔ [ .un ↦ a ]

def unmk (A :♮| Type) (u :♮| Neg A) : A ≔ (u :♮| _) .un

` unmk (mk a) reduces to a, with the (unique) key applied.
def unmk_mk (A :♮| Type) (a :♮| A) : Id A (unmk A (mk A a)) a ≔ refl a
