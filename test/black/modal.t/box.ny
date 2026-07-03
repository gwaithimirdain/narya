{` -*- narya-prog-args: ("-proofgeneral" "-coreflector") -*- `}

def f (A :□| Type) (x :□| A) : A ≔ x

` def g (A : Type) (x : A) : A := f A x

def □ (A :□| Type) : Type ≔ data [ box. (x :□| A) ]

def □map (A B :□| Type) (f :□| A → B) : □ A → □ B ≔ [ box. x ↦ box. (f x) ]

def ε (A :□| Type) (u : □ A) : A ≔ match u [ box. x ↦ x ]

` def η (A :□| Type) (x : A) : □ A := box. x

def △ (A :□| Type) (u : □ A) : □ (□ A) ≔ match u [ box. x ↦ box. (box. x) ]

def □ε∘△ (A :□| Type) (u : □ A) : Id (□ A) (□map (□ A) A (ε A) (△ A u)) u
  ≔ match u [ box. x ↦ refl (box. x) ]

def ε□∘△ (A :□| Type) (u : □ A) : Id (□ A) (ε (□ A) (△ A u)) u ≔ match u [
| box. x ↦ refl (box. x)]
