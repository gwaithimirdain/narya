{` -*- narya-prog-args: ("-proofgeneral" "-functor") -*- `}

def ○ (A :○| DomType) : CodType ≔ data [ ○. (_ :○| A) ]

def ○map (A B :○| DomType) (f :○| A → B) : ○ A → ○ B ≔ [
| ○. x ↦ ○. (f x)]

{` The modal operator preserves the identity type. `}

def Id○ (A₀ :○| DomType) (A₁ :○| DomType) (A₂ :○| Id DomType A₀ A₁)
  : Id CodType (○ A₀) (○ A₁)
  ≔ Id ○ A₂

def refl_circ (A₀ :○| DomType) (A₁ :○| DomType) (A₂ :○| Id DomType A₀ A₁)
  (x₀ :○| A₀) (x₁ :○| A₁) (x₂ :○| A₂ x₀ x₁)
  : Id ○ A₂ (○. x₀) (○. x₁)
  ≔ ○. x₂

def to_Id (A :○| DomType) (x0 x1 :○| A) (u2 : ○ (Id A x0 x1))
  : Id (○ A) (○. x0) (○. x1)
  ≔ match u2 [ ○. x ↦ ○. x ]

def from_Id (A :○| DomType) (x0 x1 :○| A)
  (u2 : Id (○ A) (○. x0) (○. x1))
  : ○ (Id A x0 x1)
  ≔ match u2
    return u0 u1 u2 ↦
           match u0, u1 [ ○. x0, ○. x1 ↦ ○ (Id A x0 x1) ] [
| ○. x ⤇ ○. x.2]

def to_from_id (A :○| DomType) (x0 x1 :○| A)
  (u2 : Id (○ A) (○. x0) (○. x1))
  : Id (Id (○ A) (○. x0) (○. x1))
      (to_Id A x0 x1 (from_Id A x0 x1 u2)) u2
  ≔ match u2
    return u0 u1 u2 ↦
           match u0, u1 [
           | ○. x0, ○. x1 ↦
               Id (Id (○ A) (○. x0) (○. x1))
                 (to_Id A x0 x1 (from_Id A x0 x1 u2)) u2] [
| ○. x ⤇ refl (○. x.2)]

def from_to_Id (A :○| DomType) (x0 x1 :○| A) (u2 : ○ (Id A x0 x1))
  : Id (○ (Id A x0 x1)) (from_Id A x0 x1 (to_Id A x0 x1 u2)) u2
  ≔ match u2 [ ○. x ↦ refl (○. x) ]
