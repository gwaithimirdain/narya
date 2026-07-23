{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br" "-functor") -*- `}

section dom ≔

  def isFibrant (A : DomType) : DomType ≔ codata [
  | x .trr.p : A.0 → A.1
  | x .trl.p : A.1 → A.0
  | x .liftr.p : (a₀ : A.0) → A.2 a₀ (x.2 .trr a₀)
  | x .liftl.p : (a₁ : A.1) → A.2 (x.2 .trl a₁) a₁
  | x .id.p : (a₀ : A.0) (a₁ : A.1) → isFibrant (A.2 a₀ a₁) ]

end

section cod ≔

  def eq (A : CodType) (a : A) : A → CodType ≔ data [ rfl. : eq A a a ]

  def cat (A : CodType) (x y z : A) (u : eq A x y) (v : eq A y z)
    : eq A x z
    ≔ match v [ rfl. ↦ u ]

  def cat3 (A : CodType) (x y z w : A) (p : eq A x y) (q : eq A y z)
    (r : eq A z w)
    : eq A x w
    ≔ match q, r [ rfl., rfl. ↦ p ]

  def idl (A : CodType) (a0 a1 : A) (a2 : eq A a0 a1)
    : eq (eq A a0 a1) (cat A a0 a0 a1 rfl. a2) a2
    ≔ match a2 [ rfl. ↦ rfl. ]

  def inv (A : CodType) (a0 a1 : A) (a2 : eq A a0 a1) : eq A a1 a0
    ≔ match a2 [ rfl. ↦ rfl. ]

  def ap (A B : CodType) (f : A → B) (a0 a1 : A) (a2 : eq A a0 a1)
    : eq B (f a0) (f a1)
    ≔ match a2 [ rfl. ↦ rfl. ]

  def ap_ap (A B C : CodType) (f : A → B) (g : B → C) (a0 a1 : A)
    (a2 : eq A a0 a1)
    : eq (eq C (g (f a0)) (g (f a1)))
        (ap B C g (f a0) (f a1) (ap A B f a0 a1 a2))
        (ap A C (x ↦ g (f x)) a0 a1 a2)
    ≔ match a2 [ rfl. ↦ rfl. ]

  def trr (A : CodType) (P : A → CodType) (a0 a1 : A) (a2 : eq A a0 a1)
    (p : P a0)
    : P a1
    ≔ match a2 [ rfl. ↦ p ]


  def trr_ap (A B : CodType) (P : A → CodType) (Q : B → CodType)
    (f : A → B) (g : (x : A) → P x → Q (f x)) (a0 a1 : A) (a2 : eq A a0 a1)
    (p : P a0)
    : eq (Q (f a1)) (g a1 (trr A P a0 a1 a2 p))
        (trr B Q (f a0) (f a1) (ap A B f a0 a1 a2) (g a0 p))
    ≔ match a2 [ rfl. ↦ rfl. ]

  def trr2 (A : CodType) (B : CodType) (P : A → B → CodType) (a0 a1 : A)
    (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a0 b0)
    : P a1 b1
    ≔ match a2, b2 [ rfl., rfl. ↦ p ]

  def trl2 (A : CodType) (B : CodType) (P : A → B → CodType) (a0 a1 : A)
    (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a1 b1)
    : P a0 b0
    ≔ match a2, b2 [ rfl., rfl. ↦ p ]

  def trr2_ap (A B : CodType) (P : A → B → CodType) (C D : CodType)
    (Q : C → D → CodType) (f : A → C) (g : B → D)
    (h : (x : A) (y : B) → P x y → Q (f x) (g y)) (a0 a1 : A)
    (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a0 b0)
    : eq (Q (f a1) (g b1)) (h a1 b1 (trr2 A B P a0 a1 a2 b0 b1 b2 p))
        (trr2 C D Q (f a0) (f a1) (ap A C f a0 a1 a2) (g b0) (g b1)
           (ap B D g b0 b1 b2) (h a0 b0 p))
    ≔ match a2, b2 [ rfl., rfl. ↦ rfl. ]

  def whiskerR (A : CodType) (a0 a1 a2 : A) (a01 a01' : eq A a0 a1)
    (a02 : eq (eq A a0 a1) a01 a01') (a12 : eq A a1 a2)
    : eq (eq A a0 a2) (cat A a0 a1 a2 a01 a12) (cat A a0 a1 a2 a01' a12)
    ≔ match a12 [ rfl. ↦ a02 ]

  def unwhiskerR (A : CodType) (a0 a1 a2 : A) (a01 a01' : eq A a0 a1)
    (a12 : eq A a1 a2)
    (a02 : eq (eq A a0 a2) (cat A a0 a1 a2 a01 a12)
             (cat A a0 a1 a2 a01' a12))
    : eq (eq A a0 a1) a01 a01'
    ≔ match a12 [ rfl. ↦ a02 ]

  def sq (A : CodType) (a00 : A)
    : (a01 : A) (a02 : eq A a00 a01) (a10 a11 : A) (a12 : eq A a10 a11)
      (a20 : eq A a00 a10) (a21 : eq A a01 a11)
      → CodType
    ≔ data [
  | rfl. : sq A a00 a00 rfl. a00 a00 rfl. rfl. rfl. ]

  section sq ≔

    def hrfl (A : CodType) (a0 a1 : A) (a2 : eq A a0 a1)
      : sq A a0 a0 rfl. a1 a1 rfl. a2 a2
      ≔ match a2 [ rfl. ↦ rfl. ]

    def nat_toid (A : CodType) (f : A → A) (p : (x : A) → eq A (f x) x)
      (a0 a1 : A) (a2 : eq A a0 a1)
      : sq A (f a0) (f a1) (ap A A f a0 a1 a2) a0 a1 a2 (p a0) (p a1)
      ≔ match a2 [ rfl. ↦ hrfl A (f a0) a0 (p a0) ]

    def ap (A B : CodType) (f : A → B) (a00 a01 : A) (a02 : eq A a00 a01)
      (a10 a11 : A) (a12 : eq A a10 a11) (a20 : eq A a00 a10)
      (a21 : eq A a01 a11) (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
      : sq B (f a00) (f a01) (ap A B f a00 a01 a02) (f a10) (f a11)
          (ap A B f a10 a11 a12) (ap A B f a00 a10 a20)
          (ap A B f a01 a11 a21)
      ≔ match a22 [ rfl. ↦ rfl. ]

    def act02 (A : CodType) (a00 a01 : A) (a02 : eq A a00 a01)
      (a10 a11 : A) (a12 : eq A a10 a11) (a20 : eq A a00 a10)
      (a21 : eq A a01 a11) (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
      (a02' : eq A a00 a01) (p : eq (eq A a00 a01) a02 a02')
      : sq A a00 a01 a02' a10 a11 a12 a20 a21
      ≔ match p [ rfl. ↦ a22 ]

    def act20 (A : CodType) (a00 a01 : A) (a02 : eq A a00 a01)
      (a10 a11 : A) (a12 : eq A a10 a11) (a20 : eq A a00 a10)
      (a21 : eq A a01 a11) (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
      (a20' : eq A a00 a10) (p : eq (eq A a00 a10) a20 a20')
      : sq A a00 a01 a02 a10 a11 a12 a20' a21
      ≔ match p [ rfl. ↦ a22 ]

    def to_cat (A : CodType) (a00 a01 : A) (a02 : eq A a00 a01)
      (a10 a11 : A) (a12 : eq A a10 a11) (a20 : eq A a00 a10)
      (a21 : eq A a01 a11) (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
      : eq (eq A a00 a11) (cat A a00 a01 a11 a02 a21)
          (cat A a00 a10 a11 a20 a12)
      ≔ match a22 [ rfl. ↦ rfl. ]

    def to_cat3 (A : CodType) (a00 a01 : A) (a02 : eq A a00 a01)
      (a10 a11 : A) (a12 : eq A a10 a11) (a20 : eq A a00 a10)
      (a21 : eq A a01 a11) (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
      : eq (eq A a10 a11) a12
          (cat3 A a10 a00 a01 a11 (inv A a00 a10 a20) a02 a21)
      ≔ match a22 [ rfl. ↦ rfl. ]

    def all_rfl_21 (A : CodType) (a : A) (a2 : eq A a a)
      (a22 : sq A a a rfl. a a rfl. rfl. a2)
      : eq (eq A a a) a2 rfl.
      ≔ cat (eq A a a) a2 (cat A a a a rfl. a2) rfl.
          (inv (eq A a a) (cat A a a a rfl. a2) a2 (idl A a a a2))
          (to_cat A a a rfl. a a rfl. rfl. a2 a22)

    def unact21 (A : CodType) (a00 a01 : A) (a02 : eq A a00 a01)
      (a10 a11 : A) (a12 : eq A a10 a11) (a20 : eq A a00 a10)
      (a21 : eq A a01 a11) (a22 : sq A a00 a01 a02 a10 a11 a12 a20 a21)
      (a21' : eq A a01 a11) (a22' : sq A a00 a01 a02 a10 a11 a12 a20 a21')
      : eq (eq A a01 a11) a21 a21'
      ≔ match a22 [
    | rfl. ↦ inv (eq A a00 a00) a21' rfl. (all_rfl_21 A a00 a21' a22')]

    def cancel_12_eq_21 (A : CodType) (a00 a01 : A) (a02 : eq A a00 a01)
      (a11 : A) (a12 : eq A a01 a11) (a20 : eq A a00 a01)
      (a22 : sq A a00 a01 a02 a01 a11 a12 a20 a12)
      : eq (eq A a00 a01) a02 a20
      ≔ unwhiskerR A a00 a01 a11 a02 a20 a12
          (to_cat A a00 a01 a02 a01 a11 a12 a20 a12 a22)

  end

  def selfnat (A : CodType) (f : A → A) (H : (x : A) → eq A (f x) x)
    (a : A)
    : eq (eq A (f (f a)) (f a)) (ap A A f (f a) a (H a)) (H (f a))
    ≔ sq.cancel_12_eq_21 A (f (f a)) (f a) (ap A A f (f a) a (H a)) a (H a)
        (H (f a)) (sq.nat_toid A f H (f a) a (H a))

  def isFibrant (A : CodType) : CodType ≔ codata [
  | x .trr.p : A.0 → A.1
  | x .trl.p : A.1 → A.0
  | x .liftr.p : (a₀ : A.0) → A.2 a₀ (x.2 .trr a₀)
  | x .liftl.p : (a₁ : A.1) → A.2 (x.2 .trl a₁) a₁
  | x .id.p : (a₀ : A.0) (a₁ : A.1) → isFibrant (A.2 a₀ a₁) ]

end

def eqv (A B : CodType) : CodType ≔ sig (
  to : A → B,
  fro : B → A,
  fro_to : (a : A) → cod.eq A (fro (to a)) a,
  to_fro : (b : B) → cod.eq B (to (fro b)) b,
  to_fro_to : (a : A)
              → cod.eq (cod.eq B (to (fro (to a))) (to a))
                  (cod.ap A B to (fro (to a)) a (fro_to a)) (to_fro (to a)) )

notation(1) A "≅" B ≔ eqv A B

def fro_to_fro (A B : CodType) (e : A ≅ B) (y : B)
  : cod.eq (cod.eq A (e .fro (e .to (e .fro y))) (e .fro y))
      (cod.ap B A (e .fro) (e .to (e .fro y)) y (e .to_fro y))
      (e .fro_to (e .fro y))
  ≔
  let f ≔ e .to in
  let g ≔ e .fro in
  let ap_f ≔ cod.ap A B f in
  let ap_g ≔ cod.ap B A g in
  let fg : B → B ≔ x ↦ e .to (e .fro x) in
  let ap_fg ≔ cod.ap B B fg in
  let gf : A → A ≔ x ↦ e .fro (e .to x) in
  let ap_gf ≔ cod.ap A A gf in
  let gfg : B → A ≔ x ↦ e .fro (e .to (e .fro x)) in
  let ap_gfg ≔ cod.ap B A gfg in
  let fgfg : B → B ≔ x ↦ e .to (e .fro (e .to (e .fro x))) in
  let gfgfg : B → A ≔ x ↦ e .fro (e .to (e .fro (e .to (e .fro x)))) in
  let η ≔ e .fro_to in
  let ε ≔ e .to_fro in
  cod.sq.unact21 A (gfgfg y) (gfg y)
    (cod.ap A A gf (gfg y) (g y) (ap_g (fg y) y (ε y))) (gfg y) (g y)
    (ap_g (fg y) y (ε y)) (η (gfg y)) (ap_g (fg y) y (ε y))
    (cod.sq.act20 A (gfgfg y) (gfg y)
       (cod.ap A A gf (gfg y) (g y) (ap_g (fg y) y (ε y))) (gfg y) (g y)
       (ap_g (fg y) y (ε y)) (ap_g (fgfg y) (fg y) (ε (fg y)))
       (ap_g (fg y) y (ε y))
       (cod.sq.act02 A (gfgfg y) (gfg y)
          (ap_g (fgfg y) (fg y) (ap_fg (fg y) y (ε y))) (gfg y) (g y)
          (ap_g (fg y) y (ε y)) (ap_g (fgfg y) (fg y) (ε (fg y)))
          (ap_g (fg y) y (ε y))
          (cod.sq.ap B A g (fgfg y) (fg y) (ap_fg (fg y) y (ε y)) (fg y) y
             (ε y) (ε (fg y)) (ε y) (cod.sq.nat_toid B fg ε (fg y) y (ε y)))
          (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
          (cod.cat (cod.eq A (gfgfg y) (gfg y))
             (ap_g (fgfg y) (fg y) (ap_fg (fg y) y (ε y)))
             (ap_gfg (fg y) y (ε y))
             (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
             (cod.ap_ap B B A fg g (fg y) y (ε y))
             (cod.inv (cod.eq A (gfgfg y) (gfg y))
                (ap_gf (gfg y) (g y) (ap_g (fg y) y (ε y)))
                (ap_gfg (fg y) y (ε y))
                (cod.ap_ap B A A g gf (fg y) y (ε y))))) (η (gfg y))
       (cod.cat3 (cod.eq A (gfgfg y) (gfg y))
          (ap_g (fgfg y) (fg y) (ε (fg y)))
          (ap_g (fgfg y) (fg y) (ap_f (gfg y) (g y) (η (g y))))
          (cod.ap A A gf (gfg y) (g y) (η (g y))) (η (gfg y))
          (cod.inv (cod.eq A (gfgfg y) (gfg y))
             (ap_g (fgfg y) (fg y) (ap_f (gfg y) (g y) (η (g y))))
             (ap_g (fgfg y) (fg y) (ε (fg y)))
             (cod.ap (cod.eq B (fgfg y) (fg y))
                (cod.eq A (gfgfg y) (gfg y)) (ap_g (fgfg y) (fg y))
                (ap_f (gfg y) (g y) (η (g y))) (ε (fg y))
                (e .to_fro_to (g y))))
          (cod.ap_ap A B A f g (gfg y) (g y) (η (g y)))
          (cod.selfnat A gf η (g y)))) (η (g y))
    (cod.sq.nat_toid A gf η (gfg y) (g y) (ap_g (fg y) y (ε y)))

def adjointify (A B : CodType) (f : A → B) (g : B → A)
  (η : (a : A) → cod.eq A (g (f a)) a) (ε : (b : B) → cod.eq B (f (g b)) b)
  : A ≅ B
  ≔
  let ap_f ≔ cod.ap A B f in
  let ap_g ≔ cod.ap B A g in
  let fg : B → B ≔ x ↦ f (g x) in
  let ap_fg ≔ cod.ap B B fg in
  let gf : A → A ≔ x ↦ g (f x) in
  let ap_gf ≔ cod.ap A A gf in
  let fgf : A → B ≔ x ↦ f (g (f x)) in
  let ap_fgf ≔ cod.ap A B fgf in
  let gfg : B → A ≔ x ↦ g (f (g x)) in
  let ap_gfg ≔ cod.ap B A gfg in
  let gfgf : A → A ≔ x ↦ g (f (g (f x))) in
  let fgfg : B → B ≔ x ↦ f (g (f (g x))) in
  let fgfgf : A → B ≔ x ↦ f (g (f (g (f x)))) in
  let gfgfg : B → A ≔ x ↦ g (f (g (f (g x)))) in
  (to ≔ f,
   fro ≔ g,
   fro_to ≔ η,
   to_fro ≔ b ↦
     cod.cat3 B (fg b) (fgfg b) (fg b) b
       (cod.inv B (fgfg b) (fg b) (ε (fg b)))
       (ap_f (gfg b) (g b) (η (g b))) (ε b),
   to_fro_to ≔ a ↦
     cod.sq.to_cat3 B (fgfgf a) (fgf a) (ap_f (gfgf a) (gf a) (η (gf a)))
       (fgf a) (f a) (ap_f (gf a) a (η a)) (ε (fgf a)) (ε (f a))
       (cod.sq.act02 B (fgfgf a) (fgf a)
          (ap_fg (fgf a) (f a) (ap_f (gf a) a (η a))) (fgf a) (f a)
          (ap_f (gf a) a (η a)) (ε (fgf a)) (ε (f a))
          (cod.sq.nat_toid B fg ε (fgf a) (f a) (ap_f (gf a) a (η a)))
          (ap_f (gfgf a) (gf a) (η (gf a)))
          (cod.cat3 (cod.eq B (fgfgf a) (fgf a))
             (ap_fg (fgf a) (f a) (ap_f (gf a) a (η a)))
             (ap_fgf (gf a) a (η a))
             (ap_f (gfgf a) (gf a) (ap_gf (gf a) a (η a)))
             (ap_f (gfgf a) (gf a) (η (gf a)))
             (cod.ap_ap A B B f fg (gf a) a (η a))
             (cod.inv (cod.eq B (fgfgf a) (fgf a))
                (ap_f (gfgf a) (gf a) (ap_gf (gf a) a (η a)))
                (ap_fgf (gf a) a (η a))
                (cod.ap_ap A A B gf f (gf a) a (η a)))
             (cod.ap (cod.eq A (gfgf a) (gf a))
                (cod.eq B (fgfgf a) (fgf a)) (ap_f (gfgf a) (gf a))
                (ap_gf (gf a) a (η a)) (η (gf a)) (cod.selfnat A gf η a)))))

{` An Id of equalities induces an equality involving transport `}
def Id_eq (A0 A1 : CodType) (A2 : Br CodType A0 A1) (a00 : A0) (a01 : A1)
  (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : cod.eq A0 a00 a10) (a21 : cod.eq A1 a01 a11)
  (a22 : Br cod.eq A2 a02 a12 a20 a21)
  : cod.eq (A2 a10 a11)
      (cod.trr2 A0 A1 (x y ↦ A2 x y) a00 a10 a20 a01 a11 a21 a02) a12
  ≔ match a22 [ rfl. ⤇ rfl. ]

{` An Id of equivalences induces an equivalence on Ids. `}
def Id_eqv (A0 : CodType) (A1 : CodType) (A2 : Br CodType A0 A1)
  (B0 : CodType) (B1 : CodType) (B2 : Br CodType B0 B1) (e0 : A0 ≅ B0)
  (e1 : A1 ≅ B1) (e2 : Br eqv A2 B2 e0 e1) (b0 : B0) (b1 : B1)
  : A2 (e0 .fro b0) (e1 .fro b1) ≅ B2 b0 b1
  ≔
  let f0 ≔ e0 .to in
  let g0 ≔ e0 .fro in
  let ap_g0 ≔ cod.ap B0 A0 g0 in
  let fg0 : B0 → B0 ≔ x ↦ f0 (g0 x) in
  let gfg0 : B0 → A0 ≔ x ↦ g0 (f0 (g0 x)) in
  let ε0 ≔ e0 .to_fro in
  let η0 ≔ e0 .fro_to in
  let f1 ≔ e1 .to in
  let g1 ≔ e1 .fro in
  let ap_g1 ≔ cod.ap B1 A1 g1 in
  let fg1 : B1 → B1 ≔ x ↦ f1 (g1 x) in
  let gfg1 : B1 → A1 ≔ x ↦ g1 (f1 (g1 x)) in
  let ε1 ≔ e1 .to_fro in
  let η1 ≔ e1 .fro_to in
  let f2 ≔ e2 .to in
  let g2 ≔ e2 .fro in
  let η2 ≔ e2 .fro_to in
  let ε2 ≔ e2 .to_fro in
  adjointify (A2 (g0 b0) (g1 b1)) (B2 b0 b1)
    (a2 ↦
     cod.trr2 B0 B1 (b0 b1 ↦ B2 b0 b1) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1
       (ε1 b1) (f2 a2)) (b2 ↦ g2 b2)
    (a2 ↦
     cod.cat (A2 (g0 b0) (g1 b1))
       (g2
          (cod.trr2 B0 B1 (x y ↦ B2 x y) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1
             (ε1 b1) (f2 a2)))
       (cod.trr2 A0 A1 (x y ↦ A2 x y) (gfg0 b0) (g0 b0)
          (ap_g0 (fg0 b0) b0 (ε0 b0)) (gfg1 b1) (g1 b1)
          (ap_g1 (fg1 b1) b1 (ε1 b1)) (g2 (f2 a2))) a2
       (cod.trr2_ap B0 B1 (x y ↦ B2 x y) A0 A1 (x y ↦ A2 x y) g0 g1
          (x0 x1 x2 ↦ g2 x2) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1 (ε1 b1)
          (f2 a2))
       (Id_eq A0 A1 A2 (gfg0 b0) (gfg1 b1) (g2 (f2 a2)) (g0 b0) (g1 b1) a2
          (ap_g0 (fg0 b0) b0 (ε0 b0)) (ap_g1 (fg1 b1) b1 (ε1 b1))
          (cod.trl2 (cod.eq A0 (gfg0 b0) (g0 b0))
             (cod.eq A1 (gfg1 b1) (g1 b1))
             (u v ↦ Br cod.eq A2 (g2 (f2 a2)) a2 u v)
             (ap_g0 (fg0 b0) b0 (ε0 b0)) (η0 (g0 b0))
             (fro_to_fro A0 B0 e0 b0) (ap_g1 (fg1 b1) b1 (ε1 b1))
             (η1 (g1 b1)) (fro_to_fro A1 B1 e1 b1) (η2 a2))))
    (b2 ↦
     Id_eq B0 B1 B2 (fg0 b0) (fg1 b1) (f2 (g2 b2)) b0 b1 b2 (ε0 b0) (ε1 b1)
       (ε2 b2))

{` Fibrancy transports across equivalences. `}
def 𝕗eqv (A B : CodType) (e : A ≅ B) (𝕗A : cod.isFibrant A)
  : cod.isFibrant B
  ≔ [
| .trr.p ↦ b0 ↦ e.1 .to (𝕗A.2 .trr (e.0 .fro b0))
| .trl.p ↦ b1 ↦ e.0 .to (𝕗A.2 .trl (e.1 .fro b1))
| .liftr.p ↦ b0 ↦
    cod.trr B.0 (b ↦ B.2 b (e.1 .to (𝕗A.2 .trr (e.0 .fro b0))))
      (e.0 .to (e.0 .fro b0)) b0 (e.0 .to_fro b0)
      (e.2 .to (𝕗A.2 .liftr (e.0 .fro b0)))
| .liftl.p ↦ b1 ↦
    cod.trr B.1 (b ↦ B.2 (e.0 .to (𝕗A.2 .trl (e.1 .fro b1))) b)
      (e.1 .to (e.1 .fro b1)) b1 (e.1 .to_fro b1)
      (e.2 .to (𝕗A.2 .liftl (e.1 .fro b1)))
| .id.p ↦ b0 b1 ↦
    𝕗eqv (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
      (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)
      (𝕗A.2 .id (e.0 .fro b0) (e.1 .fro b1))]

def Π (A :○| DomType) (B : (_ :○| A) → CodType) : CodType ≔ (x :○| A) → B x

def id_Π_iso (A0 :○| DomType) (A1 :○| DomType) (A2 :○| Br DomType A0 A1)
  (B0 : (_ :○| A0) → CodType) (B1 : (_ :○| A1) → CodType)
  (B2 : Br Π A2 {_ ↦ CodType} {_ ↦ CodType} (_ ⤇ rel CodType) B0 B1)
  (f0 : (a0 :○| A0) → B0 a0) (f1 : (a1 :○| A1) → B1 a1)
  : ((a0 :○| A0) (a1 :○| A1) (a2 :○| A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
    ≅ Br Π A2 B2 f0 f1
  ≔ (
  to ≔ f ↦ a ⤇ f a.0 a.1 a.2,
  fro ≔ g ↦ a0 a1 a2 ↦ g a2,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Π (A :○| DomType) (B : (_ :○| A) → CodType) (𝕗A :○| dom.isFibrant A)
  (𝕗B : (x :○| A) → cod.isFibrant (B x))
  : cod.isFibrant ((x :○| A) → B x)
  ≔ [
| .trr.p ↦ f0 a1 ↦ 𝕗B.2 (𝕗A.2 .liftl a1) .trr (f0 (𝕗A.2 .trl a1))
| .trl.p ↦ f1 a0 ↦ 𝕗B.2 (𝕗A.2 .liftr a0) .trl (f1 (𝕗A.2 .trr a0))
| .liftr.p ↦ f0 ↦ a ⤇
    rel 𝕗B.2
        (sym (sym (rel 𝕗A.2) .id.1 a.2 (𝕗A.2 .liftl a.1) .liftl (rel a.1)))
      .id.1 (rel f0 (𝕗A.2⁽ᵖ¹⁾ .id.1 a.2 (𝕗A.2 .liftl a.1) .trl (rel a.1)))
        (rel (𝕗B.2 (𝕗A.2 .liftl a.1) .trr (f0 (𝕗A.2 .trl a.1))))
      .trl (𝕗B.2 (𝕗A.2 .liftl a.1) .liftr (f0 (𝕗A.2 .trl a.1)))
| .liftl.p ↦ f1 ↦ a ⤇
    rel 𝕗B.2
        (sym (sym (rel 𝕗A.2) .id.1 a.2 (𝕗A.2 .liftr a.0) .liftr (rel a.0)))
      .id.1 (rel (𝕗B.2 (𝕗A.2 .liftr a.0) .trl (f1 (𝕗A.2 .trr a.0))))
        (rel f1 (𝕗A.2⁽ᵖ¹⁾ .id.1 a.2 (𝕗A.2 .liftr a.0) .trr (rel a.0)))
      .trl (𝕗B.2 (𝕗A.2 .liftr a.0) .liftl (f1 (𝕗A.2 .trr a.0)))
| .id.p ↦ f0 f1 ↦
    𝕗eqv
      ((a0 :○| A.0) (a1 :○| A.1) (a2 :○| A.2 a0 a1)
       → B.2 a2 (f0 a0) (f1 a1)) (Br Π A.2 B.2 f0 f1)
      (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
      (𝕗Π A.0
         (a0 ↦ (a1 :○| A.1) (a2 :○| A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
         𝕗A.0
         (a0 ↦
          𝕗Π A.1 (a1 ↦ (a2 :○| A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1)) 𝕗A.1
            (a1 ↦
             𝕗Π (A.2 a0 a1) (a2 ↦ B.2 a2 (f0 a0) (f1 a1)) (𝕗A.2 .id a0 a1)
               (a2 ↦ 𝕗B.2 a2 .id (f0 a0) (f1 a1)))))]
