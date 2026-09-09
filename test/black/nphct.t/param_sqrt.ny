{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-discrete-coreflector") -*- `}

def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

def eq.ap (A B : Type) (f : A → B) (a0 a1 : A) (a2 : eq A a0 a1)
  : eq B (f a0) (f a1)
  ≔ match a2 [ rfl. ↦ rfl. ]

def eqv (A B : Type) : Type ≔ sig (
  to : A → B,
  fro : B → A,
  fro_to : (a : A) → eq A (fro (to a)) a,
  to_fro : (b : B) → eq B (to (fro b)) b,
  to_fro_to : (a : A)
              → eq (eq B (to (fro (to a))) (to a))
                  (eq.ap A B to (fro (to a)) a (fro_to a)) (to_fro (to a)) )

notation(1) A "≅" B ≔ eqv A B

def eqd (A : Type) (B : A → Type) (a0 a1 : A) (a2 : eq A a0 a1) (b0 : B a0)
  (b1 : B a1)
  : Type
  ≔ match a2 [ rfl. ↦ eq (B a0) b0 b1 ]

def eq2d (A B : Type) (C : A → B → Type) (a0 a1 : A) (a2 : eq A a0 a1)
  (b0 b1 : B) (b2 : eq B b0 b1) (c0 : C a0 b0) (c1 : C a1 b1)
  : Type
  ≔ match a2, b2 [ rfl., rfl. ↦ eq (C a0 b0) c0 c1 ]

def eqd2d (A B : Type) (C : A → B → Type)
  (D : (a : A) (b : B) → C a b → Type) (a0 a1 : A) (a2 : eq A a0 a1)
  (b0 b1 : B) (b2 : eq B b0 b1) (c0 : C a0 b0) (c1 : C a1 b1)
  (c2 : eq2d A B C a0 a1 a2 b0 b1 b2 c0 c1) (d0 : D a0 b0 c0)
  (d1 : D a1 b1 c1)
  : Type
  ≔ match a2, b2, c2 [ rfl., rfl., rfl. ↦ eq (D a0 b0 c0) d0 d1 ]

def Id_eq′ (A0 A1 : Type) (A2 : Br Type A0 A1) (a00 : A0) (a01 : A1)
  (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
  (a22 : Br eq A2 a02 a12 a20 a21)
  : eq2d A0 A1 (a0 a1 ↦ A2 a0 a1) a00 a10 a20 a01 a11 a21 a02 a12
  ≔ match a22 [ rfl. ⤇ rfl. ]

def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )

notation(2) A "×" B ≔ prod A B

def √ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x : Γ)
  : Type
  ≔ codata [
| s .fst.p : A x.0 x.1 x.2
| s .snd : B x ]

def eq_√ (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : eq Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1)
  : Type
  ≔ codata [
| e .fst.p
  : eqd2d Γ Γ (x0 x1 ↦ Br Γ x0 x1) A x0.0 x1.0 x2.0 x0.1 x1.1 x2.1 x0.2
      x1.2 (Id_eq′ Γ Γ (Br Γ) x0.0 x0.1 x0.2 x1.0 x1.1 x1.2 x2.0 x2.1 x2.2)
      (u0.2 .fst) (u1.2 .fst)
| e .snd : eqd Γ B x0 x1 x2 (u0 .snd) (u1 .snd) ]

axiom √_ext (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : eq Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1) (u2 : eq_√ Γ A B x0 x1 x2 u0 u1)
  : eqd Γ (√ Γ A B) x0 x1 x2 u0 u1

def Γhat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type)
  : Type
  ≔ sig (
  x0 : Γ,
  x1 : Γ,
  x2 : Br Γ x0 x1,
  u0 : √ Γ A B x0,
  u1 : √ Γ A B x1 )

def Ahat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (y0 y1 : Γhat Γ A B) (y2 : Br (Γhat Γ A B) y0 y1)
  : Type
  ≔ Br A (y0 .x2) (y1 .x2) (sym (y2 .x2)) (y2 .u0 .fst) (y2 .u1 .fst)

def Bhat (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (y : Γhat Γ A B)
  : Type
  ≔ A (y .x0) (y .x1) (y .x2) × Br B (y .x2) (y .u0 .snd) (y .u1 .snd)

def id_√_iso (Γ :♭| Type) (A :♭| (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) → Type)
  (B :♭| Γ → Type) (x0 x1 : Γ) (x2 : Br Γ x0 x1) (u0 : √ Γ A B x0)
  (u1 : √ Γ A B x1)
  : √ (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1)
    ≅ Br (√ Γ A B) x2 u0 u1
  ≔ (
  to ≔ v ↦ [
  | .fst.p ⤇ v.2 .fst
  | .fst.1 ⤇ v .snd .fst
  | .snd ⤇ v .snd .snd],
  fro ≔ u2 ↦ [ .fst.p ↦ u2 .fst.2 | .snd ↦ (u2 .fst.1, u2 .snd) ],
  fro_to ≔ v ↦
    √_ext (Γhat Γ A B) (Ahat Γ A B) (Bhat Γ A B) (x0, x1, x2, u0, u1)
      (x0, x1, x2, u0, u1) rfl.
      (id_√_iso Γ A B x0 x1 x2 u0 u1
       .fro (id_√_iso Γ A B x0 x1 x2 u0 u1 .to v)) v
      [ .fst.p ↦ rfl. | .snd ↦ rfl. ],
  to_fro ≔ u2 ↦ ?,
  to_fro_to ≔ ?)
