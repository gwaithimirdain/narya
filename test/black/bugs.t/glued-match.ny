option parametric ≔ arity 2, letter p, name rel Br

def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

def eq.trl2 (A : Type) (B : Type) (P : A → B → Type) (a0 a1 : A)
  (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a1 b1)
  : P a0 b0
  ≔ match a2, b2 [ rfl., rfl. ↦ p ]

def iso (A B : Type) : Type ≔ sig (
  to : A → B,
  fro : B → A,
  fro_to : (a : A) → eq A (fro (to a)) a,
  to_fro : (b : B) → eq B (to (fro b)) b )

def Id_eq_rfl (A0 A1 : Type) (A2 : Br Type A0 A1) (a00 a01 : A0)
  (a02 : eq A0 a00 a01) (a10 a11 : A1) (a12 : eq A1 a10 a11)
  (a20 : A2 a00 a10) (a21 : A2 a01 a11)
  : iso
      (eq (A2 a00 a10) a20
         (eq.trl2 A0 A1 (a0 a1 ↦ A2 a0 a1) a00 a01 a02 a10 a11 a12 a21))
      (Br eq A2 a20 a21 a02 a12)
  ≔ (
  to ≔ a22 ↦ match a02 [
  | rfl. ↦ match a12 [ rfl. ↦ match a22 [ rfl. ↦ rfl. ] ]],
  fro ≔ [ rfl. ⤇ rfl. ],
  fro_to ≔ a22 ↦ match a02, a12, a22 [ rfl., rfl., rfl. ↦ rfl. ],
  to_fro ≔ [ rfl. ⤇ rfl. ])
