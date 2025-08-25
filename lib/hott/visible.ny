def isBisim (A : Type) (B : Type) (R : A → B → Type) : Type ≔ codata [
| x .trr : A → B
| x .liftr : (a : A) → R a (x .trr a)
| x .trl : B → A
| x .liftl : (b : B) → R (x .trl b) b
| x .id.e
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1)
    (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a2 b2 r0 r1) ]

def glue (A : Type) (B : Type) (R : A → B → Type) (Rb : isBisim A B R)
  : Id Type A B
  ≔ sig x y ↦ (
  unglue : R x y )
