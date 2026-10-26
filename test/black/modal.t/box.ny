{` -*- narya-prog-args: ("-proofgeneral" "-coreflector") -*- `}

def f (A :♭| Type) (x :♭| A) : A ≔ x

` def g (A : Type) (x : A) : A := f A x

def ♭ (A :♭| Type) : Type ≔ data [ ♭. (_ :♭| A) ]

def ♭map (A B :♭| Type) (f :♭| A → B) : ♭ A → ♭ B ≔ [ ♭. x ↦ ♭. (f x) ]

def ε (A :♭| Type) (u : ♭ A) : A ≔ match u [ ♭. x ↦ x ]

` def η (A :♭| Type) (x : A) : ♭ A := ♭. x

def △ (A :♭| Type) (u : ♭ A) : ♭ (♭ A) ≔ match u [ ♭. x ↦ ♭. (♭. x) ]

def ♭ε∘△ (A :♭| Type) (u : ♭ A) : Id (♭ A) (♭map (♭ A) A (ε A) (△ A u)) u
  ≔ match u [ ♭. x ↦ refl (♭. x) ]

def ε♭∘△ (A :♭| Type) (u : ♭ A) : Id (♭ A) (ε (♭ A) (△ A u)) u ≔ match u [
| ♭. x ↦ refl (♭. x)]
