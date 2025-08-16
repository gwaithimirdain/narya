{` The code in this file is used in Parser.Hott to bootstrap the definitions of fibrancy at some types.  It isn't actually loaded from here, though, it's copied into that file as strings.  It would be better to maintain it in only one place, namely here, and load it into that file with something like ppx_blob. `}

def isFibrant : Type → Type ≔ A ↦ codata [
| x .trr.e : A.0 → A.1
| x .liftr.e : (x₀ : A.0) → A.2 x₀ (x.2 .trr x₀)
| x .trl.e : A.1 → A.0
| x .liftl.e : (x₁ : A.1) → A.2 (x.2 .trl x₁) x₁
| x .id.e : (x₀ : A.0) (x₁ : A.1) → isFibrant (A.2 x₀ x₁) ]

def eq : (A : Type) (a : A) → A → Type ≔ A a ↦ data [ rfl. : eq A a a ]

def eq.trr
  : (A : Type) (P : A → Type) (a0 a1 : A) (a2 : eq A a0 a1) (p : P a0)
    → P a1
  ≔ A P a0 a1 a2 p ↦ match a2 [ rfl. ↦ p ]

def eq.trr2
  : (A : Type) (B : Type) (P : A → B → Type) (a0 a1 : A) (a2 : eq A a0 a1)
    (b0 b1 : B) (b2 : eq B b0 b1) (p : P a0 b0)
    → P a1 b1
  ≔ A B P a0 a1 a2 b0 b1 b2 p ↦ match a2, b2 [ rfl., rfl. ↦ p ]

def rtr : (A B : Type) → Type ≔ A B ↦ sig (
  to : A → B,
  fro : B → A,
  to_fro : (b : B) → eq B (to (fro b)) b )

def Id_eq
  : (A0 A1 : Type) (A2 : Id Type A0 A1) (a00 : A0) (a01 : A1)
    (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
    (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
    (a22 : Id eq A2 a02 a12 a20 a21)
    → eq (A2 a10 a11)
        (eq.trr2 A0 A1 (x y ↦ A2 x y) a00 a10 a20 a01 a11 a21 a02) a12
  ≔ A0 A1 A2 a00 a01 a02 a10 a11 a12 a20 a21 a22 ↦ match a22 [
| rfl. ⤇ rfl.]

def Id_rtr
  : (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : Type) (B1 : Type)
    (B2 : Id Type B0 B1) (e0 : rtr A0 B0) (e1 : rtr A1 B1)
    (e2 : Id rtr A2 B2 e0 e1) (b0 : B0) (b1 : B1)
    → rtr (A2 (e0 .fro b0) (e1 .fro b1)) (B2 b0 b1)
  ≔ A0 A1 A2 B0 B1 B2 e0 e1 e2 b0 b1 ↦ (
  to ≔ a2 ↦
    eq.trr2 B0 B1 (b0 b1 ↦ B2 b0 b1) (e0 .to (e0 .fro b0)) b0
      (e0 .to_fro b0) (e1 .to (e1 .fro b1)) b1 (e1 .to_fro b1) (e2 .to a2),
  fro ≔ b2 ↦ e2 .fro b2,
  to_fro ≔ b2 ↦
    Id_eq B0 B1 B2 (e0 .to (e0 .fro b0)) (e1 .to (e1 .fro b1))
      (e2 .to (e2 .fro b2)) b0 b1 b2 (e0 .to_fro b0) (e1 .to_fro b1)
      (e2 .to_fro b2))

def fib_rtr : (A B : Type) (e : rtr A B) → isFibrant B ≔ A B e ↦ [
| .trr.e ↦ b0 ↦ e.1 .to (A.2 .trr (e.0 .fro b0))
| .trl.e ↦ b1 ↦ e.0 .to (A.2 .trl (e.1 .fro b1))
| .liftr.e ↦ b0 ↦
    eq.trr B.0 (b ↦ B.2 b (e.1 .to (A.2 .trr (e.0 .fro b0))))
      (e.0 .to (e.0 .fro b0)) b0 (e.0 .to_fro b0)
      (e.2 .to (A.2 .liftr (e.0 .fro b0)))
| .liftl.e ↦ b1 ↦
    eq.trr B.1 (b ↦ B.2 (e.0 .to (A.2 .trl (e.1 .fro b1))) b)
      (e.1 .to (e.1 .fro b1)) b1 (e.1 .to_fro b1)
      (e.2 .to (A.2 .liftl (e.1 .fro b1)))
| .id.e ↦ b0 b1 ↦
    fib_rtr (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
      (Id_rtr A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)]

def id_pi_iso
  : (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
    (B1 : A1 → Type)
    (B2
    : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A2
        {_ ↦ Type} {_ ↦ Type} (_ ⤇ refl Type) B0 B1)
    (f0 : (a0 : A0) → B0 a0) (f1 : (a1 : A1) → B1 a1)
    → rtr ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
        (Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A2 B2
           f0 f1)
  ≔ A0 A1 A2 B0 B1 B2 f0 f1 ↦ (
  to ≔ f ↦ a ⤇ f a.0 a.1 a.2,
  fro ≔ g ↦ a0 a1 a2 ↦ g a2,
  to_fro ≔ _ ↦ rfl.)

def fib_pi : (A : Type) (B : A → Type) → isFibrant ((x : A) → B x)
  ≔ A B ↦ [
| .trr.e ↦ f0 ↦ a1 ↦ B.2 (A.2 .liftl a1) .trr (f0 (A.2 .trl a1))
| .trl.e ↦ f1 ↦ a0 ↦ B.2 (A.2 .liftr a0) .trl (f1 (A.2 .trr a0))
| .liftr.e ↦ f0 ↦ a ⤇
    refl B.2 (sym (sym (refl A.2) a.2 (A.2 .liftl a.1) .liftl (refl a.1)))
        (refl f0 (A.2⁽ᵉ¹⁾ a.2 (A.2 .liftl a.1) .trl (refl a.1)))
        (refl (B.2 (A.2 .liftl a.1) .trr (f0 (A.2 .trl a.1))))
      .trl (B.2 (A.2 .liftl a.1) .liftr (f0 (A.2 .trl a.1)))
| .liftl.e ↦ f1 ↦ a ⤇
    refl B.2 (sym (sym (refl A.2) a.2 (A.2 .liftr a.0) .liftr (refl a.0)))
        (refl (B.2 (A.2 .liftr a.0) .trl (f1 (A.2 .trr a.0))))
        (refl f1 (A.2⁽ᵉ¹⁾ a.2 (A.2 .liftr a.0) .trr (refl a.0)))
      .trl (B.2 (A.2 .liftr a.0) .liftl (f1 (A.2 .trr a.0)))
| .id.e ↦ f0 f1 ↦
    fib_rtr
      ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
      (Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A.2 B.2
         f0 f1) (id_pi_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)]

def sym_rtr
  : (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
    (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
    (A22 : Id (Id Type) A02 A12 A20 A21) (a00 : A00) (a01 : A01)
    (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
    (a20 : A20 a00 a10) (a21 : A21 a01 a11)
    → rtr (A22 a02 a12 a20 a21) (sym A22 a20 a21 a02 a12)
  ≔ A00 A01 A02 A10 A11 A12 A20 A21 A22 a00 a01 a02 a10 a11 a12 a20 a21 ↦ (
  to ≔ a22 ↦ sym a22,
  fro ≔ a22 ↦ sym a22,
  to_fro ≔ _ ↦ rfl.)

def isbisim_rtr
  : (A B : Type) (R S : A → B → Type)
    (e : (a : A) (b : B) → rtr (R a b) (S a b)) (Re : isBisim A B R)
    → isBisim A B S
  ≔ A B R S e Re ↦ [
| .trr ↦ a ↦ Re .trr a
| .liftr ↦ a ↦ e a (Re .trr a) .to (Re .liftr a)
| .trl ↦ b ↦ Re .trl b
| .liftl ↦ b ↦ e (Re .trl b) b .to (Re .liftl b)
| .id.e ↦ a0 b0 s0 a1 b1 s1 ↦
    isbisim_rtr (A.2 a0 a1) (B.2 b0 b1)
      (a2 b2 ↦ R.2 a2 b2 (e.0 a0 b0 .fro s0) (e.1 a1 b1 .fro s1))
      (a2 b2 ↦ S.2 a2 b2 s0 s1)
      (a2 b2 ↦
       Id_rtr (R.0 a0 b0) (R.1 a1 b1) (R.2 a2 b2) (S.0 a0 b0) (S.1 a1 b1)
         (S.2 a2 b2) (e.0 a0 b0) (e.1 a1 b1) (e.2 a2 b2) s0 s1)
      (Re.2 .id a0 b0 (e.0 a0 b0 .fro s0) a1 b1 (e.1 a1 b1 .fro s1))]

def fib_any : (A : Type) → isFibrant A ≔ A ↦ [
| .trr.e ↦ A.2 .trr
| .liftr.e ↦ A.2 .liftr
| .trl.e ↦ A.2 .trl
| .liftl.e ↦ A.2 .liftl
| .id.e ↦ x₀ x₁ ↦ fib_any (A.2 x₀ x₁)]

def pre_univalence
  : (A : Type) (B : Type) (G : Id Type A B)
    (fibG : (a : A) (b : B) → isFibrant (G a b))
    (Ge : isBisim A B (x y ↦ G x y))
    → Id isFibrant G (fib_any A) (fib_any B)
  ≔ A B G fibG Ge ↦ [
| .trr.1 ↦ a ↦ Ge .trr a
| .trl.1 ↦ b ↦ Ge .trl b
| .liftr.1 ↦ a ↦ Ge .liftr a
| .liftl.1 ↦ b ↦ Ge .liftl b
| .id.1 ↦ a b ↦ fibG a b
| .trr.e ↦ {a0} {b0} r0 ↦ fibG.2 (A.2 .liftr a0) (B.2 .liftr b0) .trr r0
| .trl.e ↦ {a1} {b1} r1 ↦ fibG.2 (A.2 .liftl a1) (B.2 .liftl b1) .trl r1
| .liftr.e ↦ {a0} {b0} r0 ↦
    sym (fibG.2 (A.2 .liftr a0) (B.2 .liftr b0) .liftr r0)
| .liftl.e ↦ {a1} {b1} r1 ↦
    sym (fibG.2 (A.2 .liftl a1) (B.2 .liftl b1) .liftl r1)
| .id.e ↦ {a0} {b0} r0 {a1} {b1} r1 ↦
    pre_univalence (A.2 a0 a1) (B.2 b0 b1) (sym G.2 r0 r1)
      (a2 b2 ↦
       fib_rtr (G.2 a2 b2 r0 r1) (sym G.2 r0 r1 a2 b2)
         (sym_rtr A.0 A.1 A.2 B.0 B.1 B.2 G.0 G.1 G.2 a0 a1 a2 b0 b1 b2 r0
            r1))
      (isbisim_rtr (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ G.2 a2 b2 r0 r1)
         (a2 b2 ↦ sym G.2 r0 r1 a2 b2)
         (a2 b2 ↦
          sym_rtr A.0 A.1 A.2 B.0 B.1 B.2 G.0 G.1 G.2 a0 a1 a2 b0 b1 b2 r0
            r1) (Ge.2 .id a0 b0 r0 a1 b1 r1))]

def glue_rtr
  : (A B : Type) (R : A → B → Type) (Re : isBisim A B R) (a : A) (b : B)
    → rtr (R a b) (glue A B R Re a b)
  ≔ A B R Re a b ↦ (to ≔ r ↦ (r,), fro ≔ g ↦ g .0, to_fro ≔ _ ↦ rfl.)

def fib_glue
  : (A B : Type) (R : A → B → Type) (Re : isBisim A B R)
    → Id isFibrant (glue A B R Re) (fib_any A) (fib_any B)
  ≔ A B R Re ↦ [
| .trr.1 ↦ a ↦
    isbisim_rtr A B (x y ↦ R x y) (a b ↦ glue A B R Re a b)
        (glue_rtr A B R Re) Re
      .trr a
| .trl.1 ↦ b ↦
    isbisim_rtr A B (x y ↦ R x y) (a b ↦ glue A B R Re a b)
        (glue_rtr A B R Re) Re
      .trl b
| .liftr.1 ↦ a ↦
    isbisim_rtr A B (x y ↦ R x y) (a b ↦ glue A B R Re a b)
        (glue_rtr A B R Re) Re
      .liftr a
| .liftl.1 ↦ b ↦
    isbisim_rtr A B (x y ↦ R x y) (a b ↦ glue A B R Re a b)
        (glue_rtr A B R Re) Re
      .liftl b
| .id.1 ↦ a b ↦ fib_rtr (R a b) (glue A B R Re a b) (glue_rtr A B R Re a b)
| .trr.e ↦ {a0} {b0} r0 ↦
    refl fib_rtr (R.2 (A.2 .liftr a0) (B.2 .liftr b0))
        (refl glue A.2 B.2 R.2 Re.2 (A.2 .liftr a0) (B.2 .liftr b0))
        (refl glue_rtr A.2 B.2 R.2 Re.2 (A.2 .liftr a0) (B.2 .liftr b0))
      .trr r0
| .trl.e ↦ {a1} {b1} r1 ↦
    refl fib_rtr (R.2 (A.2 .liftl a1) (B.2 .liftl b1))
        (refl glue A.2 B.2 R.2 Re.2 (A.2 .liftl a1) (B.2 .liftl b1))
        (refl glue_rtr A.2 B.2 R.2 Re.2 (A.2 .liftl a1) (B.2 .liftl b1))
      .trl r1
| .liftr.e ↦ {a0} {b0} r0 ↦
    sym
      (refl fib_rtr (R.2 (A.2 .liftr a0) (B.2 .liftr b0))
           (refl glue A.2 B.2 R.2 Re.2 (A.2 .liftr a0) (B.2 .liftr b0))
           (refl glue_rtr A.2 B.2 R.2 Re.2 (A.2 .liftr a0) (B.2 .liftr b0))
       .liftr r0)
| .liftl.e ↦ {a1} {b1} r1 ↦
    sym
      (refl fib_rtr (R.2 (A.2 .liftl a1) (B.2 .liftl b1))
           (refl glue A.2 B.2 R.2 Re.2 (A.2 .liftl a1) (B.2 .liftl b1))
           (refl glue_rtr A.2 B.2 R.2 Re.2 (A.2 .liftl a1) (B.2 .liftl b1))
       .liftl r1)
| .id.e ↦ {a0} {b0} r0 {a1} {b1} r1 ↦
    pre_univalence (A.2 a0 a1) (B.2 b0 b1)
      (sym (refl glue A.2 B.2 R.2 Re.2) r0 r1)
      (a2 b2 ↦
       fib_rtr (refl glue A.2 B.2 R.2 Re.2 a2 b2 r0 r1)
         (sym (refl glue A.2 B.2 R.2 Re.2) r0 r1 a2 b2)
         (sym_rtr A.0 A.1 A.2 B.0 B.1 B.2 (glue A.0 B.0 R.0 Re.0)
            (glue A.1 B.1 R.1 Re.1) (refl glue A.2 B.2 R.2 Re.2) a0 a1 a2
            b0 b1 b2 r0 r1))
      (isbisim_rtr (A.2 a0 a1) (B.2 b0 b1)
         (a2 b2 ↦ (refl glue A.2 B.2 R.2 Re.2) a2 b2 r0 r1)
         (a2 b2 ↦ sym (refl glue A.2 B.2 R.2 Re.2) r0 r1 a2 b2)
         (a2 b2 ↦
          sym_rtr A.0 A.1 A.2 B.0 B.1 B.2 (glue A.0 B.0 R.0 Re.0)
            (glue A.1 B.1 R.1 Re.1) (refl glue A.2 B.2 R.2 Re.2) a0 a1 a2
            b0 b1 b2 r0 r1)
         (refl isbisim_rtr A.2 B.2 {R.0} {R.1} (x y ⤇ R.2 x.2 y.2)
              {a b ↦ glue A.0 B.0 R.0 Re.0 a b}
              {a b ↦ glue A.1 B.1 R.1 Re.1 a b}
              (a b ⤇ refl glue A.2 B.2 R.2 Re.2 a.2 b.2)
              (refl glue_rtr A.2 B.2 R.2 Re.2) Re.2
          .id a0 b0 r0 a1 b1 r1))]
