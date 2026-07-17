{` -*- narya-prog-args: ("-proofgeneral" "-comonad") -*- `}

def ♭ (A :♭| Type) : Type ≔ data [ box. (_ :♭| A) ]

` The counit ε : ♭ ⇒ id lets a ♭-locked value be used directly.
def counit (A :♭| Type) (x :♭| A) : A ≔ x

def ε (A :♭| Type) (u : ♭ A) : A ≔ match u [ box. x ↦ x ]

` The comultiplication δ : ♭ ⇒ ♭∘♭.
def δ (A :♭| Type) (u : ♭ A) : ♭ (♭ A) ≔ match u [ box. x ↦ box. (box. x) ]

` The counit law holds definitionally: unboxing the outer layer of a comultiplied value gives
` back the original.
def counit_law (A :♭| Type) (u : ♭ A) : Id (♭ A) (ε (♭ A) (δ A u)) u ≔
  match u [ box. x ↦ refl (box. x) ]
