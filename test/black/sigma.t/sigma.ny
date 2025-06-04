def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

def pair (A : Type) (B : A → Type) (a : A) (b : B a) : Σ A B ≔ (a, b)

axiom A : Type
axiom B : A → Type
{`Pairs and tuples have the correct type and are equal to each other`}
axiom a : A
axiom b : B a
def ab : Σ A B ≔ (a, b)
def ab' : Σ A B ≔ pair A B a b
def ab_equals_ab' : Id (Σ A B) ab ab' ≔ refl ab
{`Projections have the correct type `}
axiom x : Σ A B
def x1 : A ≔ x .fst
def x2 : B x1 ≔ x .snd

{`Projections of pairs and tuples compute`}
def ab_fst_equals_a : Id A (ab .fst) a ≔ refl a
def ab_snd_equals_b : Id (B a) (ab .snd) b ≔ refl b
def ab'_fst_equals_a : Id A (ab' .fst) a ≔ refl a
def ab'_snd_equals_b : Id (B a) (ab' .snd) b ≔ refl b

{`Projections satisfy eta-conversion for both pairs and tuples`}
def x' : Σ A B ≔ pair A B (x .fst) (x .snd)
def x_equals_x' : Id (Σ A B) x x' ≔ refl x
def x'' : Σ A B ≔ (x .fst, x .snd)
def x_equals_x'' : Id (Σ A B) x x'' ≔ refl x

{`Identifications can be paired to give an identification of pairs`}
axiom a0 : A
axiom b0 : B a0
axiom a1 : A
axiom b1 : B a1
axiom a2 : Id A a0 a1
axiom b2 : Id B a0 a1 a2 b0 b1
def ab2 : Id (Σ A B) (a0, b0) (a1, b1) ≔ (a2, b2)

{`As for function-types, identity types of sigma-types are invariant under eta-conversion`}
def invariance1
  : Id Type (Id (Σ A B) (a0, b0) (a1, b1))
      (Id (Σ A B) (pair A B a0 b0) (a1, b1))
  ≔ refl (Id (Σ A B) (a0, b0) (a1, b1))

def invariance2
  : Id (Id (Σ A B) (a0, b0) (a1, b1)) (a2, b2)
      (refl pair A A (refl A) B B (refl B) a0 a1 a2 b0 b1 b2)
  ≔ refl (refl pair A A (refl A) B B (refl B) a0 a1 a2 b0 b1 b2)

{`And can be projected back out again to the inputs`}
def ab2_fst_equals_a2 : Id (Id A a0 a1) (ab2 .fst) a2 ≔ refl a2
def ab2_snd_equals_b2 : Id (Id B a0 a1 a2 b0 b1) (ab2 .snd) b2 ≔ refl b2

{`Refl commutes with pairing`}
def refl_comm1 : Id (Id (Σ A B) ab ab) (refl (pair A B a b)) (refl a, refl b)
  ≔ refl (refl (pair A B a b))
def refl_comm2
  : Id (Id (Σ A B) ab ab) (refl ((a, b) : Σ A B)) (refl a, refl b)
  ≔ refl (refl ((a, b) : Σ A B))

{`Sigmas can store identities and squares, and symmetry can act on them`}
axiom X : Type
axiom x00 : X
axiom x01 : X
axiom x02 : Id X x00 x01
axiom x10 : X
axiom x11 : X
axiom x12 : Id X x10 x11
axiom x20 : Id X x00 x10
axiom x21 : Id X x01 x11
axiom x22
  : Id ((x y ↦ Id X x y) : X → X → Type) x00 x01 x02 x10 x11 x12 x20 x21
axiom Y : Type
axiom y : Y
axiom s
  : Σ (Id ((x y ↦ Id X x y) : X → X → Type) x00 x01 x02 x10 x11 x12 x20 x21)
      (_ ↦ Y)

def s1s
  : Id ((x y ↦ Id X x y) : X → X → Type) x00 x10 x20 x01 x11 x21 x02 x12
  ≔ sym (s .fst)
