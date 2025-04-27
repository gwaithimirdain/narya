import "isfibrant"
import "bookhott"
import "hott_bookhott"

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` Since identity types compute only up to definitional isomorphism, in order to prove that anything is fibrant by corecursion, we need to be able to transport fibrancy across definitional isomorphisms.  In fact, we can transport it across any Book-HoTT equivalence defined using the Martin-Lof identity type. `}

{` The unit type `}

def ⊤ : Type ≔ sig ()

def id_⊤_iso (x y : ⊤) : ⊤ ≅ Id ⊤ x y ≔ (
  to ≔ _ ↦ (),
  fro ≔ _ ↦ (),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗⊤ : isFibrant ⊤ ≔ [
| .trr.e ↦ x ↦ x
| .trl.e ↦ x ↦ x
| .liftr.e ↦ _ ↦ ()
| .liftl.e ↦ _ ↦ ()
| .id.e ↦ x y ↦ 𝕗eqv ⊤ (Id ⊤ x y) (id_⊤_iso x y) 𝕗⊤]

{` Product types `}

def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )

notation 2 prod : A "×" B ≔ prod A B

def id_prod_iso (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : Type)
  (B1 : Type) (B2 : Id Type B0 B1) (a0 : A0) (a1 : A1) (b0 : B0) (b1 : B1)
  : A2 a0 a1 × B2 b0 b1 ≅ Id prod A2 B2 (a0, b0) (a1, b1)
  ≔ (
  to ≔ u ↦ (u .fst, u .snd),
  fro ≔ v ↦ (v .fst, v .snd),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗prod (A B : Type) (𝕗A : isFibrant A) (𝕗B : isFibrant B)
  : isFibrant (A × B)
  ≔ [
| .trr.e ↦ u0 ↦ (𝕗A.2 .trr.1 (u0 .fst), 𝕗B.2 .trr.1 (u0 .snd))
| .trl.e ↦ u1 ↦ (𝕗A.2 .trl.1 (u1 .fst), 𝕗B.2 .trl.1 (u1 .snd))
| .liftr.e ↦ u0 ↦ (𝕗A.2 .liftr.1 (u0 .fst), 𝕗B.2 .liftr.1 (u0 .snd))
| .liftl.e ↦ u1 ↦ (𝕗A.2 .liftl.1 (u1 .fst), 𝕗B.2 .liftl.1 (u1 .snd))
| .id.e ↦ u0 u1 ↦
    𝕗eqv (A.2 (u0 .fst) (u1 .fst) × B.2 (u0 .snd) (u1 .snd))
      (refl prod A.2 B.2 u0 u1)
      (id_prod_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (𝕗prod (A.2 (u0 .fst) (u1 .fst)) (B.2 (u0 .snd) (u1 .snd))
         (𝕗A.2 .id.1 (u0 .fst) (u1 .fst)) (𝕗B.2 .id.1 (u0 .snd) (u1 .snd)))]

{` Σ-types `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

def id_Σ_iso (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : Id Π A2 {_ ↦ Type} {_ ↦ Type} (_ ⤇ refl Type) B0 B1)
  (a0 : A0) (a1 : A1) (b0 : B0 a0) (b1 : B1 a1)
  : Σ (A2 a0 a1) (a2 ↦ B2 a2 b0 b1) ≅ Id Σ A2 B2 (a0, b0) (a1, b1)
  ≔ (
  to ≔ u ↦ (u .fst, u .snd),
  fro ≔ v ↦ (v .fst, v .snd),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Σ (A : Type) (B : A → Type) (𝕗A : isFibrant A)
  (𝕗B : (x : A) → isFibrant (B x))
  : isFibrant (Σ A B)
  ≔ [
| .trr.e ↦ u0 ↦ (
    𝕗A.2 .trr.1 (u0 .fst),
    𝕗B.2 (𝕗A.2 .liftr.1 (u0 .fst)) .trr.1 (u0 .snd))
| .trl.e ↦ u1 ↦ (
    𝕗A.2 .trl.1 (u1 .fst),
    𝕗B.2 (𝕗A.2 .liftl.1 (u1 .fst)) .trl.1 (u1 .snd))
| .liftr.e ↦ u0 ↦ (
    𝕗A.2 .liftr.1 (u0 .fst),
    𝕗B.2 (𝕗A.2 .liftr.1 (u0 .fst)) .liftr.1 (u0 .snd))
| .liftl.e ↦ u1 ↦ (
    𝕗A.2 .liftl.1 (u1 .fst),
    𝕗B.2 (𝕗A.2 .liftl.1 (u1 .fst)) .liftl.1 (u1 .snd))
| .id.e ↦ u0 u1 ↦
    𝕗eqv (Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd)))
      (Id Σ A.2 B.2 u0 u1)
      (id_Σ_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (𝕗Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd))
         (𝕗A.2 .id.1 (u0 .fst) (u1 .fst))
         (a2 ↦ 𝕗B.2 a2 .id.1 (u0 .snd) (u1 .snd)))]

{` Fibrant Σ-types `}
def Σ𝕗 (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ Σ (A .t) (a ↦ B a .t),
  f ≔ 𝕗Σ (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

{` Π-types `}

def id_Π_iso (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : Id Π A2 {_ ↦ Type} {_ ↦ Type} (_ ⤇ refl Type) B0 B1)
  (f0 : (a0 : A0) → B0 a0) (f1 : (a1 : A1) → B1 a1)
  : ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
    ≅ Id Π A2 B2 f0 f1
  ≔ (
  to ≔ f ↦ a ⤇ f a.0 a.1 a.2,
  fro ≔ g ↦ a0 a1 a2 ↦ g a2,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Π (A : Type) (B : A → Type) (𝕗A : isFibrant A)
  (𝕗B : (x : A) → isFibrant (B x))
  : isFibrant ((x : A) → B x)
  ≔ [
| .trr.e ↦ f0 a1 ↦ 𝕗B.2 (𝕗A.2 .liftl.1 a1) .trr.1 (f0 (𝕗A.2 .trl.1 a1))
| .trl.e ↦ f1 a0 ↦ 𝕗B.2 (𝕗A.2 .liftr.1 a0) .trl.1 (f1 (𝕗A.2 .trr.1 a0))
| .liftr.e ↦ f0 ↦ a ⤇
    refl 𝕗B.2
        (sym
           (sym (refl 𝕗A.2) .id.1 a.2 (𝕗A.2 .liftl.1 a.1) .liftl.1 (refl a.1)))
      .id.1
        (refl f0 (𝕗A.2⁽ᵉ¹⁾ .id.1 a.2 (𝕗A.2 .liftl.1 a.1) .trl.1 (refl a.1)))
        (refl (𝕗B.2 (𝕗A.2 .liftl.1 a.1) .trr.1 (f0 (𝕗A.2 .trl.1 a.1))))
      .trl.1 (𝕗B.2 (𝕗A.2 .liftl.1 a.1) .liftr.1 (f0 (𝕗A.2 .trl.1 a.1)))
| .liftl.e ↦ f1 ↦ a ⤇
    refl 𝕗B.2
        (sym
           (sym (refl 𝕗A.2) .id.1 a.2 (𝕗A.2 .liftr.1 a.0) .liftr.1 (refl a.0)))
      .id.1 (refl (𝕗B.2 (𝕗A.2 .liftr.1 a.0) .trl.1 (f1 (𝕗A.2 .trr.1 a.0))))
        (refl f1 (𝕗A.2⁽ᵉ¹⁾ .id.1 a.2 (𝕗A.2 .liftr.1 a.0) .trr.1 (refl a.0)))
      .trl.1 (𝕗B.2 (𝕗A.2 .liftr.1 a.0) .liftl.1 (f1 (𝕗A.2 .trr.1 a.0)))
| .id.e ↦ f0 f1 ↦
    𝕗eqv ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
      (Id Π A.2 B.2 f0 f1) (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
      (𝕗Π A.0 (a0 ↦ (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
         𝕗A.0
         (a0 ↦
          𝕗Π A.1 (a1 ↦ (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1)) 𝕗A.1
            (a1 ↦
             𝕗Π (A.2 a0 a1) (a2 ↦ B.2 a2 (f0 a0) (f1 a1)) (𝕗A.2 .id.1 a0 a1)
               (a2 ↦ 𝕗B.2 a2 .id.1 (f0 a0) (f1 a1)))))]

{` Fibrant Π-types `}
def Π𝕗 (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ (a : A .t) → B a .t,
  f ≔ 𝕗Π (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

{` Empty type `}

def ∅ : Type ≔ data []

def 𝕗∅ : isFibrant ∅ ≔ [
| .trr.e ↦ [ ]
| .trl.e ↦ [ ]
| .liftr.e ↦ [ ]
| .liftl.e ↦ [ ]
| .id.e ↦ [ ]]

{` Gel types `}

def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ (
  ungel : R a b )

def Gel_iso (A B : Type) (R : A → B → Type) (a : A) (b : B)
  : R a b ≅ Gel A B R a b
  ≔ (
  to ≔ r ↦ (r,),
  fro ≔ g ↦ g .0,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Gel (A B : Type) (R : A → B → Type)
  (𝕗R : (a : A) (b : B) → isFibrant (R a b)) (a : A) (b : B)
  : isFibrant (Gel A B R a b)
  ≔ 𝕗eqv (R a b) (Gel A B R a b) (Gel_iso A B R a b) (𝕗R a b)

{` Sum type `}

def sum (A B : Type) : Type ≔ data [ left. (_ : A) | right. (_ : B) ]

notation 1.5 sum : A "⊔" B ≔ sum A B

def sum_code (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 B1 : Type)
  (B2 : Id Type B0 B1) (u0 : A0 ⊔ B0) (u1 : A1 ⊔ B1)
  : Type
  ≔ match u0, u1 [
| left. a0, left. a1 ↦ A2 a0 a1
| left. a0, right. b1 ↦ ∅
| right. b0, left. a1 ↦ ∅
| right. b0, right. b1 ↦ B2 b0 b1]

def id_sum_iso (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 B1 : Type)
  (B2 : Id Type B0 B1) (u0 : A0 ⊔ B0) (u1 : A1 ⊔ B1)
  : sum_code A0 A1 A2 B0 B1 B2 u0 u1 ≅ Id sum A2 B2 u0 u1
  ≔ (
  to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ left. v2
  | left. a0, right. b1 ↦ match v2 [ ]
  | right. b0, left. a1 ↦ match v2 [ ]
  | right. b0, right. b1 ↦ right. v2],
  fro ≔ [ left. a2 ↦ a2 | right. b2 ↦ b2 ],
  to_fro ≔ [ left. a2 ↦ rfl. | right. b2 ↦ rfl. ],
  fro_to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ rfl.
  | left. a0, right. b1 ↦ match v2 [ ]
  | right. b0, left. a1 ↦ match v2 [ ]
  | right. b0, right. b1 ↦ rfl.],
  to_fro_to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ rfl.
  | left. a0, right. b1 ↦ match v2 [ ]
  | right. b0, left. a1 ↦ match v2 [ ]
  | right. b0, right. b1 ↦ rfl.])

def 𝕗sum (A B : Type) (𝕗A : isFibrant A) (𝕗B : isFibrant B)
  : isFibrant (A ⊔ B)
  ≔ [
| .trr.e ↦ [
  | left. a0 ↦ left. (𝕗A.2 .trr.1 a0)
  | right. b0 ↦ right. (𝕗B.2 .trr.1 b0)]
| .trl.e ↦ [
  | left. a1 ↦ left. (𝕗A.2 .trl.1 a1)
  | right. b1 ↦ right. (𝕗B.2 .trl.1 b1)]
| .liftr.e ↦ [
  | left. a0 ↦ left. (𝕗A.2 .liftr.1 a0)
  | right. b0 ↦ right. (𝕗B.2 .liftr.1 b0)]
| .liftl.e ↦ [
  | left. a1 ↦ left. (𝕗A.2 .liftl.1 a1)
  | right. b1 ↦ right. (𝕗B.2 .liftl.1 b1)]
| .id.e ↦ u0 u1 ↦ (
    𝕗eqv (sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 u1) (Id sum A.2 B.2 u0 u1)
      (id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 u0 u1)
      (match u0, u1 [
       | left. a0, left. a1 ↦ 𝕗A.2 .id.1 a0 a1
       | left. _, right. _ ↦ 𝕗∅
       | right. _, left. _ ↦ 𝕗∅
       | right. b0, right. b1 ↦ 𝕗B.2 .id.1 b0 b1]))]

{` The natural numbers `}

def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def ℕ_code (m n : ℕ) : Type ≔ match m, n [
| zero., zero. ↦ ⊤
| zero., suc. _ ↦ ∅
| suc. _, zero. ↦ ∅
| suc. m, suc. n ↦ ℕ_code m n]

def id_ℕ_iso (n0 n1 : ℕ) : ℕ_code n0 n1 ≅ Id ℕ n0 n1
  ≔ adjointify (ℕ_code n0 n1) (Id ℕ n0 n1)
      (m2 ↦
       match n0, n1 [
       | zero., zero. ↦ zero.
       | zero., suc. n1 ↦ match m2 [ ]
       | suc. n0, zero. ↦ match m2 [ ]
       | suc. n0, suc. n1 ↦ suc. (id_ℕ_iso n0 n1 .to m2)])
      ([ zero. ↦ () | suc. m2 ↦ id_ℕ_iso m2.0 m2.1 .fro m2.2 ])
      (m2 ↦
       match n0, n1 [
       | zero., zero. ↦ rfl.
       | zero., suc. n1 ↦ match m2 [ ]
       | suc. n0, zero. ↦ match m2 [ ]
       | suc. n0, suc. n1 ↦ id_ℕ_iso n0 n1 .fro_to m2])
      ([ zero. ↦ rfl.
       | suc. m2 ↦
           eq.ap (Id ℕ m2.0 m2.1) (Id ℕ (suc. m2.0) (suc. m2.1)) (x ↦ suc. x)
             (id_ℕ_iso m2.0 m2.1 .to (id_ℕ_iso m2.0 m2.1 .fro m2.2)) m2.2
             (id_ℕ_iso m2.0 m2.1 .to_fro m2.2)])

def 𝕗_ℕ_code (n0 n1 : ℕ) : isFibrant (ℕ_code n0 n1) ≔ match n0, n1 [
| zero., zero. ↦ 𝕗⊤
| zero., suc. n1 ↦ 𝕗∅
| suc. n0, zero. ↦ 𝕗∅
| suc. n0, suc. n1 ↦ 𝕗_ℕ_code n0 n1]

def 𝕗ℕ : isFibrant ℕ ≔ [
| .trr.e ↦ x ↦ x
| .trl.e ↦ x ↦ x
| .liftr.e ↦ x ↦ refl x
| .liftl.e ↦ x ↦ refl x
| .id.e ↦ n0 n1 ↦
    𝕗eqv (ℕ_code n0 n1) (Id ℕ n0 n1) (id_ℕ_iso n0 n1) (𝕗_ℕ_code n0 n1)]

{` W-types `}

{` To prove that general W-types are fibrant, we need function extensionality, since W-types involve functions as inputs. `}

axiom funext (A : Type) (B : A → Type) (f0 f1 : (x : A) → B x)
  (f2 : (x : A) → eq (B x) (f0 x) (f1 x))
  : eq ((x : A) → B x) f0 f1

{` We also need a version of funext for bridges in function types.  Since Id-Π is definitionally isomorphic to a triple Π-type, we can derive this from ordinary funext. `}

def funext_refl (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : refl ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (f0 : Π A0 B0) (f1 : Π A1 B1) (f20 f21 : refl Π A2 B2 f0 f1)
  (f22 : (a0 : A0) (a1 : A1) (a2 : A2 a0 a1)
         → eq.eq (B2 a2 (f0 a0) (f1 a1)) (f20 a2) (f21 a2))
  : eq (refl Π A2 B2 f0 f1) f20 f21
  ≔ eq.ap ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
      (refl Π A2 {x ↦ B0 x} {x ↦ B1 x} (x ⤇ B2 x.2) f0 f1)
      (g ↦ x ⤇ g x.0 x.1 x.2) (x0 x1 x2 ↦ f20 x2) (x0 x1 x2 ↦ f21 x2)
      (funext A0 (a0 ↦ (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
         (x0 x1 x2 ↦ f20 x2) (x0 x1 x2 ↦ f21 x2)
         (a0 ↦
          funext A1 (a1 ↦ (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
            (x1 x2 ↦ f20 x2) (x1 x2 ↦ f21 x2)
            (a1 ↦
             funext (A2 a0 a1) (a2 ↦ B2 a2 (f0 a0) (f1 a1)) (x2 ↦ f20 x2)
               (x2 ↦ f21 x2) (a2 ↦ f22 a0 a1 a2))))

{` Now, there are two ways to characterize the Id types of a W-type.  The firts is that the Id-types of an (indexed) W-type are an indexed W-type, which is properly indexed even if the original W-type was not.  This is not helpful for us, since indexed inductive types in general are *not* fibrant until we fibrantly replace them.  However, we include the encode-decode argument here anyway. `}

section Indexed_𝕎 ≔

  def 𝕎spec : Type ≔ sig (
    I : Type,
    A : Type,
    B : A → Type,
    j : (a : A) → B a → I,
    k : A → I )

  def 𝕎 (s : 𝕎spec) : s .I → Type ≔ data [
  | sup. (a : s .A) (f : (b : s .B a) → 𝕎 s (s .j a b)) : 𝕎 s (s .k a) ]

  def code_spec (s : 𝕎spec) : 𝕎spec ≔ (
    I ≔ sig (
      i0 : s .I,
      i1 : s .I,
      i2 : Id (s .I) i0 i1,
      x0 : 𝕎 s i0,
      x1 : 𝕎 s i1 ),
    A ≔ sig (
      a0 : s .A,
      a1 : s .A,
      a2 : Id (s .A) a0 a1,
      f0 : (b0 : s .B a0) → 𝕎 s (s .j a0 b0),
      f1 : (b1 : s .B a1) → 𝕎 s (s .j a1 b1) ),
    B ≔ x ↦ sig (
      b0 : s .B (x .a0),
      b1 : s .B (x .a1),
      b2 : refl (s .B) (x .a2) b0 b1 ),
    j ≔ a b ↦ (
      s .j (a .a0) (b .b0),
      s .j (a .a1) (b .b1),
      refl (s .j) (a .a2) (b .b2),
      a .f0 (b .b0),
      a .f1 (b .b1)),
    k ≔ a ↦ (
      s .k (a .a0),
      s .k (a .a1),
      refl (s .k) (a .a2),
      sup. (a .a0) (a .f0),
      sup. (a .a1) (a .f1)))

  def 𝕎_encode (s : 𝕎spec) (i0 i1 : s .I) (i2 : Id (s .I) i0 i1)
    (x0 : 𝕎 s i0) (x1 : 𝕎 s i1) (x2 : refl (𝕎 s) i2 x0 x1)
    : 𝕎 (code_spec s) (i0, i1, i2, x0, x1)
    ≔ match x2 [
  | sup. a f ↦
      sup. (a.0, a.1, a.2, f.0, f.1)
        (b ↦
         𝕎_encode s (s .j a.0 (b .b0)) (s .j a.1 (b .b1))
           (refl (s .j) a.2 (b .b2)) (f.0 (b .b0)) (f.1 (b .b1))
           (f.2 (b .b2)))]

  def 𝕎_decode (s : 𝕎spec) (y : code_spec s .I) (y2 : 𝕎 (code_spec s) y)
    : refl (𝕎 s) (y .i2) (y .x0) (y .x1)
    ≔ match y2 [
  | sup. a f ↦
      sup. (a .a2)
        (b ⤇
         𝕎_decode s
           (s .j (a .a0) b.0,
            s .j (a .a1) b.1,
            refl s .j (a .a2) b.2,
            a .f0 b.0,
            a .f1 b.1) (f (b.0, b.1, b.2)))]

  def 𝕎_decode_encode (s : 𝕎spec) (i0 i1 : s .I) (i2 : Id (s .I) i0 i1)
    (x0 : 𝕎 s i0) (x1 : 𝕎 s i1) (x2 : refl (𝕎 s) i2 x0 x1)
    : eq (refl (𝕎 s) i2 x0 x1)
        (𝕎_decode s (i0, i1, i2, x0, x1) (𝕎_encode s i0 i1 i2 x0 x1 x2)) x2
    ≔ match x2 [
  | sup. a f ↦
      eq.ap
        (refl Π (refl s .B a.2) {b ↦ 𝕎 s (s .j a.0 b)} {b ↦ 𝕎 s (s .j a.1 b)}
           (b ⤇ refl 𝕎 (refl s) (refl s .j a.2 b.2)) f.0 f.1)
        (refl 𝕎 (refl s) (refl s .k a.2) (sup. a.0 f.0) (sup. a.1 f.1))
        (H ↦ sup. a.2 H)
        (b ⤇
         𝕎_decode s
           (s .j a.0 b.0, s .j a.1 b.1, refl s .j a.2 b.2, f.0 b.0, f.1 b.1)
           (𝕎_encode s (s .j a.0 b.0) (s .j a.1 b.1) (refl s .j a.2 b.2)
              (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
        (funext_refl (s .B a.0) (s .B a.1) (refl s .B a.2)
           (x ↦ 𝕎 s (s .j a.0 x)) (x ↦ 𝕎 s (s .j a.1 x))
           (x ⤇ refl 𝕎 (refl s) (refl s .j a.2 x.2)) f.0 f.1
           (b ⤇
            𝕎_decode s
              (s .j a.0 b.0,
               s .j a.1 b.1,
               refl s .j a.2 b.2,
               f.0 b.0,
               f.1 b.1)
              (𝕎_encode s (s .j a.0 b.0) (s .j a.1 b.1) (refl s .j a.2 b.2)
                 (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
           (a0 a1 a2 ↦
            𝕎_decode_encode s (s .j a.0 a0) (s .j a.1 a1) (refl s .j a.2 a2)
              (f.0 a0) (f.1 a1) (f.2 a2)))]

  def 𝕎_encode_decode (s : 𝕎spec) (y : code_spec s .I)
    (y2 : 𝕎 (code_spec s) y)
    : eq (𝕎 (code_spec s) y)
        (𝕎_encode s (y .i0) (y .i1) (y .i2) (y .x0) (y .x1) (𝕎_decode s y y2))
        y2
    ≔ match y2 [
  | sup. a f ↦
      eq.ap ((b : code_spec s .B a) → 𝕎 (code_spec s) (code_spec s .j a b))
        (𝕎 (code_spec s) (code_spec s .k a)) (g ↦ sup. a g)
        (b ↦
         𝕎_encode s (s .j (a .a0) (b .b0)) (s .j (a .a1) (b .b1))
           (refl s .j (a .a2) (b .b2)) (a .f0 (b .b0)) (a .f1 (b .b1))
           (𝕎_decode s
              (s .j (a .a0) (b .b0),
               s .j (a .a1) (b .b1),
               refl s .j (a .a2) (b .b2),
               a .f0 (b .b0),
               a .f1 (b .b1)) (f (b .b0, b .b1, b .b2)))) f
        (funext (code_spec s .B a) (b ↦ 𝕎 (code_spec s) (code_spec s .j a b))
           (b ↦
            𝕎_encode s (s .j (a .a0) (b .b0)) (s .j (a .a1) (b .b1))
              (refl s .j (a .a2) (b .b2)) (a .f0 (b .b0)) (a .f1 (b .b1))
              (𝕎_decode s
                 (s .j (a .a0) (b .b0),
                  s .j (a .a1) (b .b1),
                  refl s .j (a .a2) (b .b2),
                  a .f0 (b .b0),
                  a .f1 (b .b1)) (f (b .b0, b .b1, b .b2)))) f
           (x ↦ 𝕎_encode_decode s (code_spec s .j a x) (f x)))]

  def id_𝕎_iso (s : 𝕎spec) (i0 i1 : s .I) (i2 : Id (s .I) i0 i1)
    (x0 : 𝕎 s i0) (x1 : 𝕎 s i1)
    : refl (𝕎 s) i2 x0 x1 ≅ 𝕎 (code_spec s) (i0, i1, i2, x0, x1)
    ≔ adjointify (refl (𝕎 s) i2 x0 x1) (𝕎 (code_spec s) (i0, i1, i2, x0, x1))
        (𝕎_encode s i0 i1 i2 x0 x1) (𝕎_decode s (i0, i1, i2, x0, x1))
        (x2 ↦ 𝕎_decode_encode s i0 i1 i2 x0 x1 x2)
        (y2 ↦ 𝕎_encode_decode s (i0, i1, i2, x0, x1) y2)

end

{` The characterization of Id-types of W-types that is useful to us is recursive, analogous to that for the Id-types of ℕ above. `}

def 𝕎 (A : Type) (B : A → Type) : Type ≔ data [
| sup. (a : A) (f : B a → 𝕎 A B) ]

{` We need to characterize the *dependent* Id-types over bridges of A and B. `}

def 𝕎_code (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : refl ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1)
  : Type
  ≔ match x0, x1 [
| sup. a0 f0, sup. a1 f1 ↦
    Σ (A2 a0 a1)
      (a2 ↦
       (b0 : B0 a0) (b1 : B1 a1) (b2 : B2 a2 b0 b1)
       → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))]

{` The encode-decode argument is straightforward, and only long because of the multiple applications of funext and because we lack implicit arguments. `}

def 𝕎_encode (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : refl ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1) (x2 : refl 𝕎 A2 B2 x0 x1)
  : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1
  ≔ match x2 [
| sup. a f ↦ (
    fst ≔ a.2,
    snd ≔ b0 b1 b2 ↦ 𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b0) (f.1 b1) (f.2 b2))]

def 𝕎_decode (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : refl ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1) (y2 : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
  : refl 𝕎 A2 B2 x0 x1
  ≔ match x0, x1 [
| sup. a0 f0, sup. a1 f1 ↦
    sup. (y2 .fst)
      (b ⤇ 𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b.0) (f1 b.1) (y2 .snd b.0 b.1 b.2))]

def 𝕎_decode_encode (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : refl ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1) (x2 : refl 𝕎 A2 B2 x0 x1)
  : eq (refl 𝕎 A2 B2 x0 x1)
      (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1 (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1 x2))
      x2
  ≔ match x2 [
| sup. a f ↦
    eq.ap
      (refl Π (B2 a.2) {_ ↦ 𝕎 A0 B0} {_ ↦ 𝕎 A1 B1} (_ ⤇ refl 𝕎 A2 B2) f.0 f.1)
      (refl 𝕎 A2 B2 (sup. a.0 f.0) (sup. a.1 f.1)) (g ↦ sup. a.2 g)
      (b ⤇
       𝕎_decode A0 A1 A2 B0 B1 B2 (f.0 b.0) (f.1 b.1)
         (𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
      (funext_refl (B0 a.0) (B1 a.1) (B2 a.2) (_ ↦ 𝕎 A0 B0) (_ ↦ 𝕎 A1 B1)
         (_ ⤇ refl 𝕎 A2 B2) f.0 f.1
         (b ⤇
          𝕎_decode A0 A1 A2 B0 B1 B2 (f.0 b.0) (f.1 b.1)
            (𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
         (a0 a1 a2 ↦
          𝕎_decode_encode A0 A1 A2 B0 B1 B2 (f.0 a0) (f.1 a1) (f.2 a2)))]

def 𝕎_encode_decode (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : refl ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1) (y2 : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
  : eq (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1 (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1 y2))
      y2
  ≔ match x0, x1 [
| sup. a0 f0, sup. a1 f1 ↦
    eq.ap
      ((b0 : B0 a0) (b1 : B1 a1) (b2 : B2 (y2 .fst) b0 b1)
       → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
      (Σ (A2 a0 a1)
         (a2 ↦
          (b0 : B0 a0) (b1 : B1 a1) (b2 : B2 a2 b0 b1)
          → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))) (f2 ↦ (y2 .fst, f2))
      ((𝕎_encode A0 A1 A2 B0 B1 B2 (sup. a0 f0) (sup. a1 f1)
          (sup. (y2 .fst)
             (b ⤇
              𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b.0) (f1 b.1)
                (y2 .snd b.0 b.1 b.2)))) .snd) (y2 .snd)
      (funext (B0 a0)
         (b0 ↦
          (b1 : B1 a1) (b2 : B2 (y2 .fst) b0 b1)
          → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
         (𝕎_encode A0 A1 A2 B0 B1 B2 (sup. a0 f0) (sup. a1 f1)
            (sup. (y2 .fst)
               (b ⤇
                𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b.0) (f1 b.1)
                  (y2 .snd b.0 b.1 b.2))) .snd) (y2 .snd)
         (b0 ↦
          funext (B1 a1)
            (b1 ↦
             (b2 : B2 (y2 .fst) b0 b1)
             → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
            (𝕎_encode A0 A1 A2 B0 B1 B2 (sup. a0 f0) (sup. a1 f1)
                 (sup. (y2 .fst)
                    (b ⤇
                     𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b.0) (f1 b.1)
                       (y2 .snd b.0 b.1 b.2)))
             .snd b0) (y2 .snd b0)
            (b1 ↦
             funext (B2 (y2 .fst) b0 b1)
               (_ ↦ 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
               (𝕎_encode A0 A1 A2 B0 B1 B2 (sup. a0 f0) (sup. a1 f1)
                    (sup. (y2 .fst)
                       (b ⤇
                        𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b.0) (f1 b.1)
                          (y2 .snd b.0 b.1 b.2)))
                .snd b0 b1) (y2 .snd b0 b1)
               (b2 ↦
                𝕎_encode_decode A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1)
                  (y2 .snd b0 b1 b2)))))]

def Id_𝕎_iso (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : refl ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1)
  : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1 ≅ refl 𝕎 A2 B2 x0 x1
  ≔ adjointify (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1) (refl 𝕎 A2 B2 x0 x1)
      (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1) (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_encode_decode A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_decode_encode A0 A1 A2 B0 B1 B2 x0 x1)

{` Next we prove that the codes are fibrant if the inputs are.  This is just putting together 𝕗Σ and 𝕗Π. `}

def 𝕗_𝕎_code (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : refl ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (𝕗A0 : isFibrant A0) (𝕗A1 : isFibrant A1) (𝕗A2 : refl isFibrant A2 𝕗A0 𝕗A1)
  (𝕗B0 : (a0 : A0) → isFibrant (B0 a0)) (𝕗B1 : (a1 : A1) → isFibrant (B1 a1))
  (𝕗B2 : refl Π A2 {x ↦ isFibrant (B0 x)} {x ↦ isFibrant (B1 x)}
           (x ⤇ refl isFibrant (B2 x.2)) 𝕗B0 𝕗B1) (x0 : 𝕎 A0 B0)
  (x1 : 𝕎 A1 B1)
  : isFibrant (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
  ≔ match x0, x1 [
| sup. a0 f0, sup. a1 f1 ↦
    𝕗Σ (A2 a0 a1)
      (a2 ↦
       (b0 : B0 a0) (b1 : B1 a1) (b2 : B2 a2 b0 b1)
       → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1)) (𝕗A2 .id.1 a0 a1)
      (a2 ↦
       𝕗Π (B0 a0)
         (b0 ↦
          (b1 : B1 a1) (b2 : B2 a2 b0 b1)
          → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1)) (𝕗B0 a0)
         (b0 ↦
          𝕗Π (B1 a1)
            (b1 ↦
             (b2 : B2 a2 b0 b1) → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
            (𝕗B1 a1)
            (b1 ↦
             𝕗Π (B2 a2 b0 b1) (_ ↦ 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
               (𝕗B2 a2 .id.1 b0 b1)
               (b2 ↦
                𝕗_𝕎_code A0 A1 A2 B0 B1 B2 𝕗A0 𝕗A1 𝕗A2 𝕗B0 𝕗B1 𝕗B2 (f0 b0)
                  (f1 b1)))))]

{` Finally, we can prove that W-types are fibrant.  Note that there are "recursive calls" to 𝕗𝕎 in *all* the clauses.  I'm not exactly sure how they are justified in the cases of tr and lift, but note that they are inside matches as well.  `}

def 𝕗𝕎 (A : Type) (B : A → Type) (𝕗A : isFibrant A)
  (𝕗B : (x : A) → isFibrant (B x))
  : isFibrant (𝕎 A B)
  ≔ [
| .trr.e ↦ [
  | sup. a0 f0 ↦
      sup. (𝕗A.2 .trr.1 a0)
        (refl 𝕗Π (B.2 (𝕗A.2 .liftr.1 a0)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
             (_ ⤇ refl 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 .liftr.1 a0))
             {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
             (_ ⤇ refl 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2)
         .trr.1 f0)]
| .trl.e ↦ [
  | sup. a1 f1 ↦
      sup. (𝕗A.2 .trl.1 a1)
        (refl 𝕗Π (B.2 (𝕗A.2 .liftl.1 a1)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
             (_ ⤇ refl 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 .liftl.1 a1))
             {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
             (_ ⤇ refl 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2)
         .trl.1 f1)]
| .liftr.e ↦ [
  | sup. a0 f0 ↦
      sup. (𝕗A.2 .liftr.1 a0)
        (refl 𝕗Π (B.2 (𝕗A.2 .liftr.1 a0)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
             (_ ⤇ refl 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 .liftr.1 a0))
             {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
             (_ ⤇ refl 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2)
         .liftr.1 f0)]
| .liftl.e ↦ [
  | sup. a1 f1 ↦
      sup. (𝕗A.2 .liftl.1 a1)
        (refl 𝕗Π (B.2 (𝕗A.2 .liftl.1 a1)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
             (_ ⤇ refl 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 .liftl.1 a1))
             {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
             (_ ⤇ refl 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2)
         .liftl.1 f1)]
| .id.e ↦ x0 x1 ↦
    𝕗eqv (𝕎_code A.0 A.1 A.2 B.0 B.1 B.2 x0 x1) (refl 𝕎 A.2 B.2 x0 x1)
      (Id_𝕎_iso A.0 A.1 A.2 B.0 B.1 B.2 x0 x1)
      (𝕗_𝕎_code A.0 A.1 A.2 B.0 B.1 B.2 𝕗A.0 𝕗A.1 𝕗A.2 𝕗B.0 𝕗B.1 𝕗B.2 x0 x1)]

{` M-types `}

{` The bridge types of an M-type are M-types with non-uniform parameters, so we need to treat those in generality. `}

def 𝕄_spec : Type ≔ sig (
  R : Type,
  A : R → Fib,
  B : (r : R) → A r .t → Fib,
  k : (r : R) (a : A r .t) → B r a .t → R )

def 𝕄 (s : 𝕄_spec) (r : s .R) : Type ≔ codata [
| x .recv : s .A r .t
| x .send : (b : s .B r (x .recv) .t) → 𝕄 s (s .k r (x .recv) b) ]

def 𝕄_code_spec (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1) : 𝕄_spec ≔ (
  R ≔ sig (
    r0 : s0 .R,
    r1 : s1 .R,
    r2 : s2 .R r0 r1,
    x0 : 𝕄 s0 r0,
    x1 : 𝕄 s1 r1 ),
  A ≔ r ↦
    Idd𝕗 (s0 .A (r .r0)) (s1 .A (r .r1)) (s2 .A (r .r2)) (r .x0 .recv)
      (r .x1 .recv),
  B ≔ r a2 ↦
    Σ𝕗 (s0 .B (r .r0) (r .x0 .recv))
      (b0 ↦
       Σ𝕗 (s1 .B (r .r1) (r .x1 .recv))
         (b1 ↦
          Idd𝕗 (s0 .B (r .r0) (r .x0 .recv)) (s1 .B (r .r1) (r .x1 .recv))
            (s2 .B (r .r2) a2) b0 b1)),
  k ≔ r a2 b ↦ (
    r0 ≔ s0 .k (r .r0) (r .x0 .recv) (b .0),
    r1 ≔ s1 .k (r .r1) (r .x1 .recv) (b .1 .0),
    r2 ≔ s2 .k (r .r2) a2 (b .1 .1),
    x0 ≔ r .x0 .send (b .0),
    x1 ≔ r .x1 .send (b .1 .0)))

def 𝕄_encode (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x2 : refl 𝕄 s2 r2 x0 x1)
  : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
  ≔ [
| .recv ↦ x2 .recv
| .send ↦ b ↦
    𝕄_encode s0 s1 s2 (s0 .k r0 (x0 .recv) (b .0))
      (s1 .k r1 (x1 .recv) (b .1 .0)) (s2 .k r2 (x2 .recv) (b .1 .1))
      (x0 .send (b .0)) (x1 .send (b .1 .0)) (x2 .send (b .1 .1))]

def 𝕄_decode (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
  : refl 𝕄 s2 r2 x0 x1
  ≔ [
| .recv ↦ y2 .recv
| .send ↦ b ⤇
    𝕄_decode s0 s1 s2 (s0 .k r0 (x0 .recv) b.0) (s1 .k r1 (x1 .recv) b.1)
      (s2 .k r2 (y2 .recv) b.2) (x0 .send b.0) (x1 .send b.1)
      (y2 .send (b.0, (b.1, b.2)))]

{` We need "coinductive extensionality" for eq.  The version we need says that the eq-types of 𝕄, dependent over an equality of indices, are again an 𝕄-type, similar to the codes for Id but without changing the spec.  In the application we only use this over a fixed index, but we can't *define* it in general without passing to a non-rfl equality of indices. `}

def 𝕄_bisim (s : 𝕄_spec) (r0 : s .R) (r1 : s .R) (r2 : eq (s .R) r0 r1)
  (x0 : 𝕄 s r0) (x1 : 𝕄 s r1)
  : Type
  ≔ codata [
| x2 .recv : eqd (s .R) (r ↦ s .A r .t) r0 r1 r2 (x0 .recv) (x1 .recv)
| x2 .send
  : (b0 : s .B r0 (x0 .recv) .t) (b1 : s .B r1 (x1 .recv) .t)
    (b2
    : eqdd (s .R) (r ↦ s .A r .t) (r a ↦ s .B r a .t) r0 r1 r2 (x0 .recv)
        (x1 .recv) (x2 .recv) b0 b1)
    → 𝕄_bisim s (s .k r0 (x0 .recv) b0) (s .k r1 (x1 .recv) b1)
        (ap3d (s .R) (r ↦ s .A r .t) (r a ↦ s .B r a .t) (s .R) (s .k) r0 r1
           r2 (x0 .recv) (x1 .recv) (x2 .recv) b0 b1 b2) (x0 .send b0)
        (x1 .send b1) ]

axiom 𝕄_ext (s : 𝕄_spec) (r : s .R) (x0 x1 : 𝕄 s r)
  (y2 : 𝕄_bisim s r r rfl. x0 x1)
  : eq (𝕄 s r) x0 x1

def 𝕄_encode_decode_bisim (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1)
  (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
  : 𝕄_bisim (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1) (r0, r1, r2, x0, x1)
      rfl.
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2))
      y2
  ≔ [
| .recv ↦ rfl.
| .send ↦ b0 b1 b2 ↦ match b2 [
  | rfl. ↦
      𝕄_encode_decode_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) (b0 .0))
        (s1 .k r1 (x1 .recv) (b0 .1 .0)) (s2 .k r2 (y2 .recv) (b0 .1 .1))
        (x0 .send (b0 .0)) (x1 .send (b0 .1 .0)) (y2 .send b0)]]

def 𝕄_encode_decode (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
  : eq (𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2))
      y2
  ≔ 𝕄_ext (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2))
      y2 (𝕄_encode_decode_bisim s0 s1 s2 r0 r1 r2 x0 x1 y2)

{` For the other direction we need a version of this for refl 𝕄. `}

def refl_𝕄_bisim (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r20 : s2 .R r0 r1) (r21 : s2 .R r0 r1)
  (r22 : eq (s2 .R r0 r1) r20 r21) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x20 : refl 𝕄 s2 r20 x0 x1) (x21 : refl 𝕄 s2 r21 x0 x1)
  : Type
  ≔ codata [
| y2 .recv
  : eqd (s2 .R r0 r1) (r2 ↦ s2 .A r2 .t (x0 .recv) (x1 .recv)) r20 r21 r22
      (x20 .recv) (x21 .recv)
| y2 .send
  : (b0 : s0 .B r0 (x0 .recv) .t) (b1 : s1 .B r1 (x1 .recv) .t)
    (b20 : s2 .B r20 (x20 .recv) .t b0 b1)
    (b21 : s2 .B r21 (x21 .recv) .t b0 b1)
    (b22
    : eqdd (s2 .R r0 r1) (r2 ↦ s2 .A r2 .t (x0 .recv) (x1 .recv))
        (r2 a2 ↦ s2 .B r2 a2 .t b0 b1) r20 r21 r22 (x20 .recv) (x21 .recv)
        (y2 .recv) b20 b21)
    → refl_𝕄_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) b0) (s1 .k r1 (x1 .recv) b1)
        (s2 .k r20 (x20 .recv) b20) (s2 .k r21 (x21 .recv) b21)
        (ap3d (s2 .R r0 r1) (r2 ↦ s2 .A r2 .t (x0 .recv) (x1 .recv))
           (r2 a2 ↦ s2 .B r2 a2 .t b0 b1)
           (s2 .R (s0 .k r0 (x0 .recv) b0) (s1 .k r1 (x1 .recv) b1))
           (r2 a2 b2 ↦ s2 .k r2 a2 b2) r20 r21 r22 (x20 .recv) (x21 .recv)
           (y2 .recv) b20 b21 b22) (x0 .send b0) (x1 .send b1)
        (x20 .send b20) (x21 .send b21) ]

axiom refl_𝕄_ext (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x20 : refl 𝕄 s2 r2 x0 x1) (x21 : refl 𝕄 s2 r2 x0 x1)
  (y22 : refl_𝕄_bisim s0 s1 s2 r0 r1 r2 r2 rfl. x0 x1 x20 x21)
  : eq (refl 𝕄 s2 r2 x0 x1) x20 x21

def 𝕄_decode_encode_bisim (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1)
  (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x2 : refl 𝕄 s2 r2 x0 x1)
  : refl_𝕄_bisim s0 s1 s2 r0 r1 r2 r2 rfl. x0 x1
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2))
      x2
  ≔ [
| .recv ↦ rfl.
| .send ↦ b0 b1 b20 b21 b22 ↦ match b22 [
  | rfl. ↦
      𝕄_decode_encode_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) b0)
        (s1 .k r1 (x1 .recv) b1) (s2 .k r2 (x2 .recv) b20) (x0 .send b0)
        (x1 .send b1) (x2 .send b20)]]

def 𝕄_decode_encode (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x2 : refl 𝕄 s2 r2 x0 x1)
  : eq (refl 𝕄 s2 r2 x0 x1)
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2))
      x2
  ≔ refl_𝕄_ext s0 s1 s2 r0 r1 r2 x0 x1
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2))
      x2 (𝕄_decode_encode_bisim s0 s1 s2 r0 r1 r2 x0 x1 x2)

def Id_𝕄_iso (s0 s1 : 𝕄_spec) (s2 : Id 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1) ≅ refl 𝕄 s2 r2 x0 x1
  ≔ adjointify (𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
      (refl 𝕄 s2 r2 x0 x1) (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_encode_decode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_decode_encode s0 s1 s2 r0 r1 r2 x0 x1)

{` And finally we can prove that 𝕄-types are fibrant.  Again we have "recursive calls" to 𝕗𝕄 in each of the clauses, presumably justified by some kind of productivity. `}

def 𝕗𝕄 (s : 𝕄_spec) (r : s .R) : isFibrant (𝕄 s r) ≔ [
| .trr.e ↦ x0 ↦ [
  | .recv ↦ s.2 .A r.2 .f .trr.1 (x0 .recv)
  | .send ↦
      refl 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftr.1 (x0 .recv)) .t)
          {b0 ↦ 𝕄 s.0 (s.0 .k r.0 (x0 .recv) b0)}
          {b1 ↦ 𝕄 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr.1 (x0 .recv)) b1)}
          (b2 ⤇
           refl 𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr.1 (x0 .recv)) b2))
          (s.2 .B r.2 (s.2 .A r.2 .f .liftr.1 (x0 .recv)) .f)
          {b0 ↦ 𝕗𝕄 s.0 (s.0 .k r.0 (x0 .recv) b0)}
          {b1 ↦ 𝕗𝕄 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr.1 (x0 .recv)) b1)}
          (b2 ⤇
           refl 𝕗𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr.1 (x0 .recv)) b2))
        .trr.1 (b0 ↦ x0 .send b0)]
| .trl.e ↦ x1 ↦ [
  | .recv ↦ s.2 .A r.2 .f .trl.1 (x1 .recv)
  | .send ↦
      refl 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftl.1 (x1 .recv)) .t)
          {b0 ↦ 𝕄 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl.1 (x1 .recv)) b0)}
          {b1 ↦ 𝕄 s.1 (s.1 .k r.1 (x1 .recv) b1)}
          (b2 ⤇
           refl 𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl.1 (x1 .recv)) b2))
          (s.2 .B r.2 (s.2 .A r.2 .f .liftl.1 (x1 .recv)) .f)
          {b0 ↦ 𝕗𝕄 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl.1 (x1 .recv)) b0)}
          {b1 ↦ 𝕗𝕄 s.1 (s.1 .k r.1 (x1 .recv) b1)}
          (b2 ⤇
           refl 𝕗𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl.1 (x1 .recv)) b2))
        .trl.1 (b1 ↦ x1 .send b1)]
| .liftr.e ↦ x0 ↦ [
  | .recv ↦ s.2 .A r.2 .f .liftr.1 (x0 .recv)
  | .send ↦
      refl 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftr.1 (x0 .recv)) .t)
          {b0 ↦ 𝕄 s.0 (s.0 .k r.0 (x0 .recv) b0)}
          {b1 ↦ 𝕄 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr.1 (x0 .recv)) b1)}
          (b2 ⤇
           refl 𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr.1 (x0 .recv)) b2))
          (s.2 .B r.2 (s.2 .A r.2 .f .liftr.1 (x0 .recv)) .f)
          {b0 ↦ 𝕗𝕄 s.0 (s.0 .k r.0 (x0 .recv) b0)}
          {b1 ↦ 𝕗𝕄 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr.1 (x0 .recv)) b1)}
          (b2 ⤇
           refl 𝕗𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr.1 (x0 .recv)) b2))
        .liftr.1 (b0 ↦ x0 .send b0)]
| .liftl.e ↦ x1 ↦ [
  | .recv ↦ s.2 .A r.2 .f .liftl.1 (x1 .recv)
  | .send ↦
      refl 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftl.1 (x1 .recv)) .t)
          {b0 ↦ 𝕄 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl.1 (x1 .recv)) b0)}
          {b1 ↦ 𝕄 s.1 (s.1 .k r.1 (x1 .recv) b1)}
          (b2 ⤇
           refl 𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl.1 (x1 .recv)) b2))
          (s.2 .B r.2 (s.2 .A r.2 .f .liftl.1 (x1 .recv)) .f)
          {b0 ↦ 𝕗𝕄 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl.1 (x1 .recv)) b0)}
          {b1 ↦ 𝕗𝕄 s.1 (s.1 .k r.1 (x1 .recv) b1)}
          (b2 ⤇
           refl 𝕗𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl.1 (x1 .recv)) b2))
        .liftl.1 (b1 ↦ x1 .send b1)]
| .id.e ↦ x0 x1 ↦
    𝕗eqv (𝕄 (𝕄_code_spec s.0 s.1 s.2) (r.0, r.1, r.2, x0, x1))
      (refl 𝕄 s.2 r.2 x0 x1) (Id_𝕄_iso s.0 s.1 s.2 r.0 r.1 r.2 x0 x1)
      (𝕗𝕄 (𝕄_code_spec s.0 s.1 s.2) (r.0, r.1, r.2, x0, x1))]
