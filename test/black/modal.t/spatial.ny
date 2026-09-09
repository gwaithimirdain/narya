{` -*- narya-prog-args: ("-proofgeneral" "-spatial") -*- `}

` The coreflector ♭ can be unlocked directly (comonad counit).
def f (A :♭| Type) (x :♭| A) : A ≔ x

` The reflector ♯ cannot be unlocked directly: it has no counit of its own.
` def ε (A :♯| Type) (x :♯| A) : A := x

` A plain value can supply a ♯-locked field (monad unit).
def sharp : Type ≔ data [ sharp. (_ :♯| Type) ]

def wsh (x : Type) : sharp ≔ sharp. x

` A plain value cannot supply a bare ♭-locked field: ♭ has no unit of its own.
` def flat : Type := data [ flat. (_ :♭| Type) ]
` def wfl (x : Type) : flat := flat. x

` Counit of the adjunction ♭ ⊣ ♯: a ♭∘♯-locked variable can be unlocked directly.
def counit (A : ♭ ♯ | Type) (x : ♭ ♯ | A) : A ≔ x

` The other order has no such cell.
` def nocounit (A :♯ ♭| Type) (x :♯ ♭| A) : A := x

` Unit of the adjunction: a plain value can supply a ♯∘♭-locked field.
def unit : Type ≔ data [ unit. (_ : ♯ ♭ | Type) ]

def wu (x : Type) : unit ≔ unit. x

` The other order has no such cell.
` def unit2 : Type := data [ unit2. (_ :♭ ♯| Type) ]
` def wu2 (x : Type) : unit2 := unit2. x
