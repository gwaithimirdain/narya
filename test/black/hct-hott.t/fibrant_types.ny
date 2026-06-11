{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "bookhott"
import "hott_bookhott"

{` Since identity types compute only up to definitional isomorphism, in order to prove that anything is fibrant by corecursion, we need to be able to transport fibrancy across definitional isomorphisms.  In fact, we can transport it across any Book-HoTT equivalence defined using the Martin-Lof identity type. `}

{` The unit type `}

def ⊤ : Type ≔ sig ()

def id_⊤_iso (x y : ⊤) : ⊤ ≅ Br ⊤ x y ≔ (
  to ≔ _ ↦ (),
  fro ≔ _ ↦ (),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗⊤ : isFibrant ⊤ ≔ [
| .trr.p ↦ x ↦ x
| .trl.p ↦ x ↦ x
| .liftr.p ↦ _ ↦ ()
| .liftl.p ↦ _ ↦ ()
| .id.p ↦ x y ↦ 𝕗eqv ⊤ (Br ⊤ x y) (id_⊤_iso x y) 𝕗⊤]

def ⊤𝕗 : Fib ≔ (⊤, 𝕗⊤)

{` Product types `}

def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )

notation(2) A "×" B ≔ prod A B

def id_prod_iso (A0 : Type) (A1 : Type) (A2 : Br Type A0 A1) (B0 : Type)
  (B1 : Type) (B2 : Br Type B0 B1) (a0 : A0) (a1 : A1) (b0 : B0) (b1 : B1)
  : A2 a0 a1 × B2 b0 b1 ≅ Br prod A2 B2 (a0, b0) (a1, b1)
  ≔ (
  to ≔ u ↦ (u .fst, u .snd),
  fro ≔ v ↦ (v .fst, v .snd),
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗prod (A B : Type) (𝕗A : isFibrant A) (𝕗B : isFibrant B)
  : isFibrant (A × B)
  ≔ [
| .trr.p ↦ u0 ↦ (𝕗A.2 .trr (u0 .fst), 𝕗B.2 .trr (u0 .snd))
| .trl.p ↦ u1 ↦ (𝕗A.2 .trl (u1 .fst), 𝕗B.2 .trl (u1 .snd))
| .liftr.p ↦ u0 ↦ (𝕗A.2 .liftr (u0 .fst), 𝕗B.2 .liftr (u0 .snd))
| .liftl.p ↦ u1 ↦ (𝕗A.2 .liftl (u1 .fst), 𝕗B.2 .liftl (u1 .snd))
| .id.p ↦ u0 u1 ↦
    𝕗eqv (A.2 (u0 .fst) (u1 .fst) × B.2 (u0 .snd) (u1 .snd))
      (rel prod A.2 B.2 u0 u1)
      (id_prod_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (𝕗prod (A.2 (u0 .fst) (u1 .fst)) (B.2 (u0 .snd) (u1 .snd))
         (𝕗A.2 .id (u0 .fst) (u1 .fst)) (𝕗B.2 .id (u0 .snd) (u1 .snd)))]

def prod𝕗 (A B : Fib) : Fib ≔ (
  A .t × B .t,
  𝕗prod (A .t) (B .t) (A .f) (B .f))

notation(2) A "×𝕗" B ≔ prod𝕗 A B

{` Σ-types `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

def id_Σ_iso (A0 : Type) (A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : (A2 ⇒ rel Type) B0 B1)
  (a0 : A0) (a1 : A1) (b0 : B0 a0) (b1 : B1 a1)
  : Σ (A2 a0 a1) (a2 ↦ B2 a2 b0 b1) ≅ Br Σ A2 B2 (a0, b0) (a1, b1)
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
| .trr.p ↦ u0 ↦ (
    𝕗A.2 .trr (u0 .fst),
    𝕗B.2 (𝕗A.2 .liftr (u0 .fst)) .trr (u0 .snd))
| .trl.p ↦ u1 ↦ (
    𝕗A.2 .trl (u1 .fst),
    𝕗B.2 (𝕗A.2 .liftl (u1 .fst)) .trl (u1 .snd))
| .liftr.p ↦ u0 ↦ (
    𝕗A.2 .liftr (u0 .fst),
    𝕗B.2 (𝕗A.2 .liftr (u0 .fst)) .liftr (u0 .snd))
| .liftl.p ↦ u1 ↦ (
    𝕗A.2 .liftl (u1 .fst),
    𝕗B.2 (𝕗A.2 .liftl (u1 .fst)) .liftl (u1 .snd))
| .id.p ↦ u0 u1 ↦
    𝕗eqv (Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd)))
      (Br Σ A.2 B.2 u0 u1)
      (id_Σ_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 .fst) (u1 .fst) (u0 .snd)
         (u1 .snd))
      (𝕗Σ (A.2 (u0 .fst) (u1 .fst)) (a2 ↦ B.2 a2 (u0 .snd) (u1 .snd))
         (𝕗A.2 .id (u0 .fst) (u1 .fst))
         (a2 ↦ 𝕗B.2 a2 .id (u0 .snd) (u1 .snd)))]

{` Fibrant Σ-types `}
def Σ𝕗 (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ Σ (A .t) (a ↦ B a .t),
  f ≔ 𝕗Σ (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

{` Π-types `}

def Π (A : Type) (B : A → Type) : Type := (x : A) → B x

def id_Π_iso (A0 : Type) (A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type)
  (B2 : Br Π A2 {_ ↦ Type} {_ ↦ Type} (_ ⤇ rel Type) B0 B1)
  (f0 : (a0 : A0) → B0 a0) (f1 : (a1 : A1) → B1 a1)
  : ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
    ≅ Br Π A2 B2 f0 f1
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
    𝕗eqv ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
      (Br Π A.2 B.2 f0 f1) (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
      (𝕗Π A.0 (a0 ↦ (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
         𝕗A.0
         (a0 ↦
          𝕗Π A.1 (a1 ↦ (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1)) 𝕗A.1
            (a1 ↦
             𝕗Π (A.2 a0 a1) (a2 ↦ B.2 a2 (f0 a0) (f1 a1)) (𝕗A.2 .id a0 a1)
               (a2 ↦ 𝕗B.2 a2 .id (f0 a0) (f1 a1)))))]

{` Fibrant Π-types `}
def Π𝕗 (A : Fib) (B : A .t → Fib) : Fib ≔ (
  t ≔ (a : A .t) → B a .t,
  f ≔ 𝕗Π (A .t) (a ↦ B a .t) (A .f) (a ↦ B a .f))

{` Empty type `}

def ∅ : Type ≔ data []

def 𝕗∅ : isFibrant ∅ ≔ [
| .trr.p ↦ [ ]
| .trl.p ↦ [ ]
| .liftr.p ↦ [ ]
| .liftl.p ↦ [ ]
| .id.p ↦ [ ]]

{` Gel types `}

def Gel (A B : Type) (R : A → B → Type) : Br Type A B ≔ sig a b ↦ (
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

notation(1.5) A "⊔" B ≔ sum A B

def sum_code (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 B1 : Type)
  (B2 : Br Type B0 B1) (u0 : A0 ⊔ B0) (u1 : A1 ⊔ B1)
  : Type
  ≔ match u0, u1 [
| left. a0, left. a1 ↦ A2 a0 a1
| left. a0, right. b1 ↦ ∅
| right. b0, left. a1 ↦ ∅
| right. b0, right. b1 ↦ B2 b0 b1]

def id_sum_iso (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 B1 : Type)
  (B2 : Br Type B0 B1) (u0 : A0 ⊔ B0) (u1 : A1 ⊔ B1)
  : sum_code A0 A1 A2 B0 B1 B2 u0 u1 ≅ Br sum A2 B2 u0 u1
  ≔ (
  to ≔ v2 ↦ match u0, u1 [
  | left. a0, left. a1 ↦ left. v2
  | left. a0, right. b1 ↦ match v2 [ ]
  | right. b0, left. a1 ↦ match v2 [ ]
  | right. b0, right. b1 ↦ right. v2],
  fro ≔ [ left. a ⤇ a.2 | right. b ⤇ b.2 ],
  to_fro ≔ [ left. a ⤇ rfl. | right. b ⤇ rfl. ],
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
| .trr.p ↦ [
  | left. a0 ↦ left. (𝕗A.2 .trr a0)
  | right. b0 ↦ right. (𝕗B.2 .trr b0)]
| .trl.p ↦ [
  | left. a1 ↦ left. (𝕗A.2 .trl a1)
  | right. b1 ↦ right. (𝕗B.2 .trl b1)]
| .liftr.p ↦ [
  | left. a0 ↦ left. (𝕗A.2 .liftr a0)
  | right. b0 ↦ right. (𝕗B.2 .liftr b0)]
| .liftl.p ↦ [
  | left. a1 ↦ left. (𝕗A.2 .liftl a1)
  | right. b1 ↦ right. (𝕗B.2 .liftl b1)]
| .id.p ↦ u0 u1 ↦ (
    𝕗eqv (sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 u1) (Br sum A.2 B.2 u0 u1)
      (id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 u0 u1)
      (match u0, u1 [
       | left. a0, left. a1 ↦ 𝕗A.2 .id a0 a1
       | left. _, right. _ ↦ 𝕗∅
       | right. _, left. _ ↦ 𝕗∅
       | right. b0, right. b1 ↦ 𝕗B.2 .id b0 b1]))]

{` The natural numbers `}

def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def ℕ_code (m n : ℕ) : Type ≔ match m, n [
| zero., zero. ↦ ⊤
| zero., suc. _ ↦ ∅
| suc. _, zero. ↦ ∅
| suc. m, suc. n ↦ ℕ_code m n]

def id_ℕ_iso (n0 n1 : ℕ) : ℕ_code n0 n1 ≅ Br ℕ n0 n1
  ≔ adjointify (ℕ_code n0 n1) (Br ℕ n0 n1)
      (m2 ↦
       match n0, n1 [
       | zero., zero. ↦ zero.
       | zero., suc. n1 ↦ match m2 [ ]
       | suc. n0, zero. ↦ match m2 [ ]
       | suc. n0, suc. n1 ↦ suc. (id_ℕ_iso n0 n1 .to m2)])
      ([ zero. ⤇ () | suc. m ⤇ id_ℕ_iso m.0 m.1 .fro m.2 ])
      (m2 ↦
       match n0, n1 [
       | zero., zero. ↦ rfl.
       | zero., suc. n1 ↦ match m2 [ ]
       | suc. n0, zero. ↦ match m2 [ ]
       | suc. n0, suc. n1 ↦ id_ℕ_iso n0 n1 .fro_to m2])
      ([ zero. ⤇ rfl.
       | suc. m ⤇
           eq.ap (Br ℕ m.0 m.1) (Br ℕ (suc. m.0) (suc. m.1)) (x ↦ suc. x)
             (id_ℕ_iso m.0 m.1 .to (id_ℕ_iso m.0 m.1 .fro m.2)) m.2
             (id_ℕ_iso m.0 m.1 .to_fro m.2)])

def 𝕗_ℕ_code (n0 n1 : ℕ) : isFibrant (ℕ_code n0 n1) ≔ match n0, n1 [
| zero., zero. ↦ 𝕗⊤
| zero., suc. n1 ↦ 𝕗∅
| suc. n0, zero. ↦ 𝕗∅
| suc. n0, suc. n1 ↦ 𝕗_ℕ_code n0 n1]

def 𝕗ℕ : isFibrant ℕ ≔ [
| .trr.p ↦ x ↦ x
| .trl.p ↦ x ↦ x
| .liftr.p ↦ x ↦ rel x
| .liftl.p ↦ x ↦ rel x
| .id.p ↦ n0 n1 ↦
    𝕗eqv (ℕ_code n0 n1) (Br ℕ n0 n1) (id_ℕ_iso n0 n1) (𝕗_ℕ_code n0 n1)]

{` W-types `}

{` To prove that general W-types are fibrant, we need function extensionality, since W-types involve functions as inputs. `}

axiom funext (A : Type) (B : A → Type) (f0 f1 : (x : A) → B x)
  (f2 : (x : A) → eq (B x) (f0 x) (f1 x))
  : eq ((x : A) → B x) f0 f1

{` We also need a version of funext for bridges in function types.  Since Id-Π is definitionally isomorphic to a triple Π-type, we can derive this from ordinary funext. `}

def funext_refl (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : rel ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (f0 : Π A0 B0) (f1 : Π A1 B1) (f20 f21 : rel Π A2 B2 f0 f1)
  (f22 : (a0 : A0) (a1 : A1) (a2 : A2 a0 a1)
         → eq.eq (B2 a2 (f0 a0) (f1 a1)) (f20 a2) (f21 a2))
  : eq (rel Π A2 B2 f0 f1) f20 f21
  ≔ eq.ap ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
      (rel Π A2 {x ↦ B0 x} {x ↦ B1 x} (x ⤇ B2 x.2) f0 f1)
      (g ↦ x ⤇ g x.0 x.1 x.2) (x0 x1 x2 ↦ f20 x2) (x0 x1 x2 ↦ f21 x2)
      (funext A0 (a0 ↦ (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
         (x0 x1 x2 ↦ f20 x2) (x0 x1 x2 ↦ f21 x2)
         (a0 ↦
          funext A1 (a1 ↦ (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
            (x1 x2 ↦ f20 x2) (x1 x2 ↦ f21 x2)
            (a1 ↦
             funext (A2 a0 a1) (a2 ↦ B2 a2 (f0 a0) (f1 a1)) (x2 ↦ f20 x2)
               (x2 ↦ f21 x2) (a2 ↦ f22 a0 a1 a2))))

{` Now, there are two ways to characterize the Br types of a W-type.  The firts is that the Id-types of an (indexed) W-type are an indexed W-type, which is properly indexed even if the original W-type was not.  This is not helpful for us, since indexed inductive types in general are *not* fibrant until we fibrantly replace them.  However, we include the encode-decode argument here anyway. `}

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
      i2 : Br (s .I) i0 i1,
      x0 : 𝕎 s i0,
      x1 : 𝕎 s i1 ),
    A ≔ sig (
      a0 : s .A,
      a1 : s .A,
      a2 : Br (s .A) a0 a1,
      f0 : (b0 : s .B a0) → 𝕎 s (s .j a0 b0),
      f1 : (b1 : s .B a1) → 𝕎 s (s .j a1 b1) ),
    B ≔ x ↦ sig (
      b0 : s .B (x .a0),
      b1 : s .B (x .a1),
      b2 : rel (s .B) (x .a2) b0 b1 ),
    j ≔ a b ↦ (
      s .j (a .a0) (b .b0),
      s .j (a .a1) (b .b1),
      rel (s .j) (a .a2) (b .b2),
      a .f0 (b .b0),
      a .f1 (b .b1)),
    k ≔ a ↦ (
      s .k (a .a0),
      s .k (a .a1),
      rel (s .k) (a .a2),
      sup. (a .a0) (a .f0),
      sup. (a .a1) (a .f1)))

  def 𝕎_encode (s : 𝕎spec) (i0 i1 : s .I) (i2 : Br (s .I) i0 i1)
    (x0 : 𝕎 s i0) (x1 : 𝕎 s i1) (x2 : rel (𝕎 s) i2 x0 x1)
    : 𝕎 (code_spec s) (i0, i1, i2, x0, x1)
    ≔ match x2 [
  | sup. a f ⤇
      sup. (a.0, a.1, a.2, f.0, f.1)
        (b ↦
         𝕎_encode s (s .j a.0 (b .b0)) (s .j a.1 (b .b1))
           (rel (s .j) a.2 (b .b2)) (f.0 (b .b0)) (f.1 (b .b1))
           (f.2 (b .b2)))]

  def 𝕎_decode (s : 𝕎spec) (y : code_spec s .I) (y2 : 𝕎 (code_spec s) y)
    : rel (𝕎 s) (y .i2) (y .x0) (y .x1)
    ≔ match y2 [
  | sup. a f ↦
      sup. (a .a2)
        (b ⤇
         𝕎_decode s
           (s .j (a .a0) b.0,
            s .j (a .a1) b.1,
            rel s .j (a .a2) b.2,
            a .f0 b.0,
            a .f1 b.1) (f (b.0, b.1, b.2)))]

  def 𝕎_decode_encode (s : 𝕎spec) (i0 i1 : s .I) (i2 : Br (s .I) i0 i1)
    (x0 : 𝕎 s i0) (x1 : 𝕎 s i1) (x2 : rel (𝕎 s) i2 x0 x1)
    : eq (rel (𝕎 s) i2 x0 x1)
        (𝕎_decode s (i0, i1, i2, x0, x1) (𝕎_encode s i0 i1 i2 x0 x1 x2)) x2
    ≔ match x2 [
  | sup. a f ⤇
      eq.ap
        (rel Π (rel s .B a.2) {b ↦ 𝕎 s (s .j a.0 b)} {b ↦ 𝕎 s (s .j a.1 b)}
           (b ⤇ rel 𝕎 (rel s) (rel s .j a.2 b.2)) f.0 f.1)
        (rel 𝕎 (rel s) (rel s .k a.2) (sup. a.0 f.0) (sup. a.1 f.1))
        (H ↦ sup. a.2 H)
        (b ⤇
         𝕎_decode s
           (s .j a.0 b.0, s .j a.1 b.1, rel s .j a.2 b.2, f.0 b.0, f.1 b.1)
           (𝕎_encode s (s .j a.0 b.0) (s .j a.1 b.1) (rel s .j a.2 b.2)
              (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
        (funext_refl (s .B a.0) (s .B a.1) (rel s .B a.2)
           (x ↦ 𝕎 s (s .j a.0 x)) (x ↦ 𝕎 s (s .j a.1 x))
           (x ⤇ rel 𝕎 (rel s) (rel s .j a.2 x.2)) f.0 f.1
           (b ⤇
            𝕎_decode s
              (s .j a.0 b.0,
               s .j a.1 b.1,
               rel s .j a.2 b.2,
               f.0 b.0,
               f.1 b.1)
              (𝕎_encode s (s .j a.0 b.0) (s .j a.1 b.1) (rel s .j a.2 b.2)
                 (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
           (a0 a1 a2 ↦
            𝕎_decode_encode s (s .j a.0 a0) (s .j a.1 a1) (rel s .j a.2 a2)
              (f.0 a0) (f.1 a1) (f.2 a2)))]

  def 𝕎_encode_decode (s : 𝕎spec) (y : code_spec s .I)
    (y2 : 𝕎 (code_spec s) y)
    : eq (𝕎 (code_spec s) y)
        (𝕎_encode s (y .i0) (y .i1) (y .i2) (y .x0) (y .x1)
           (𝕎_decode s y y2)) y2
    ≔ match y2 [
  | sup. a f ↦
      eq.ap ((b : code_spec s .B a) → 𝕎 (code_spec s) (code_spec s .j a b))
        (𝕎 (code_spec s) (code_spec s .k a)) (g ↦ sup. a g)
        (b ↦
         𝕎_encode s (s .j (a .a0) (b .b0)) (s .j (a .a1) (b .b1))
           (rel s .j (a .a2) (b .b2)) (a .f0 (b .b0)) (a .f1 (b .b1))
           (𝕎_decode s
              (s .j (a .a0) (b .b0),
               s .j (a .a1) (b .b1),
               rel s .j (a .a2) (b .b2),
               a .f0 (b .b0),
               a .f1 (b .b1)) (f (b .b0, b .b1, b .b2)))) f
        (funext (code_spec s .B a)
           (b ↦ 𝕎 (code_spec s) (code_spec s .j a b))
           (b ↦
            𝕎_encode s (s .j (a .a0) (b .b0)) (s .j (a .a1) (b .b1))
              (rel s .j (a .a2) (b .b2)) (a .f0 (b .b0)) (a .f1 (b .b1))
              (𝕎_decode s
                 (s .j (a .a0) (b .b0),
                  s .j (a .a1) (b .b1),
                  rel s .j (a .a2) (b .b2),
                  a .f0 (b .b0),
                  a .f1 (b .b1)) (f (b .b0, b .b1, b .b2)))) f
           (x ↦ 𝕎_encode_decode s (code_spec s .j a x) (f x)))]

  def id_𝕎_iso (s : 𝕎spec) (i0 i1 : s .I) (i2 : Br (s .I) i0 i1)
    (x0 : 𝕎 s i0) (x1 : 𝕎 s i1)
    : rel (𝕎 s) i2 x0 x1 ≅ 𝕎 (code_spec s) (i0, i1, i2, x0, x1)
    ≔ adjointify (rel (𝕎 s) i2 x0 x1)
        (𝕎 (code_spec s) (i0, i1, i2, x0, x1)) (𝕎_encode s i0 i1 i2 x0 x1)
        (𝕎_decode s (i0, i1, i2, x0, x1))
        (x2 ↦ 𝕎_decode_encode s i0 i1 i2 x0 x1 x2)
        (y2 ↦ 𝕎_encode_decode s (i0, i1, i2, x0, x1) y2)

end

{` The characterization of Id-types of W-types that is useful to us is recursive, analogous to that for the Id-types of ℕ above. `}

def 𝕎 (A : Type) (B : A → Type) : Type ≔ data [
| sup. (a : A) (f : B a → 𝕎 A B) ]

{` We need to characterize the *dependent* Id-types over bridges of A and B. `}

def 𝕎_code (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : rel ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1)
  : Type
  ≔ match x0, x1 [
| sup. a0 f0, sup. a1 f1 ↦
    Σ (A2 a0 a1)
      (a2 ↦
       (b0 : B0 a0) (b1 : B1 a1) (b2 : B2 a2 b0 b1)
       → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))]

{` The encode-decode argument is straightforward, and only long because of the multiple applications of funext and because we lack implicit arguments. `}

def 𝕎_encode (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : rel ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1) (x2 : rel 𝕎 A2 B2 x0 x1)
  : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1
  ≔ match x2 [
| sup. a f ⤇ (
    fst ≔ a.2,
    snd ≔ b0 b1 b2 ↦ 𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b0) (f.1 b1) (f.2 b2))]

def 𝕎_decode (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : rel ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1) (y2 : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
  : rel 𝕎 A2 B2 x0 x1
  ≔ match x0, x1 [
| sup. a0 f0, sup. a1 f1 ↦
    sup. (y2 .fst)
      (b ⤇
       𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b.0) (f1 b.1) (y2 .snd b.0 b.1 b.2))]

def 𝕎_decode_encode (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : rel ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1) (x2 : rel 𝕎 A2 B2 x0 x1)
  : eq (rel 𝕎 A2 B2 x0 x1)
      (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1
         (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1 x2)) x2
  ≔ match x2 [
| sup. a f ⤇
    eq.ap
      (rel Π (B2 a.2) {_ ↦ 𝕎 A0 B0} {_ ↦ 𝕎 A1 B1} (_ ⤇ rel 𝕎 A2 B2) f.0 f.1)
      (rel 𝕎 A2 B2 (sup. a.0 f.0) (sup. a.1 f.1)) (g ↦ sup. a.2 g)
      (b ⤇
       𝕎_decode A0 A1 A2 B0 B1 B2 (f.0 b.0) (f.1 b.1)
         (𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
      (funext_refl (B0 a.0) (B1 a.1) (B2 a.2) (_ ↦ 𝕎 A0 B0) (_ ↦ 𝕎 A1 B1)
         (_ ⤇ rel 𝕎 A2 B2) f.0 f.1
         (b ⤇
          𝕎_decode A0 A1 A2 B0 B1 B2 (f.0 b.0) (f.1 b.1)
            (𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
         (a0 a1 a2 ↦
          𝕎_decode_encode A0 A1 A2 B0 B1 B2 (f.0 a0) (f.1 a1) (f.2 a2)))]

def 𝕎_encode_decode (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : rel ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1) (y2 : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
  : eq (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1
         (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1 y2)) y2
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

def Id_𝕎_iso (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : rel ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (x0 : 𝕎 A0 B0) (x1 : 𝕎 A1 B1)
  : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1 ≅ rel 𝕎 A2 B2 x0 x1
  ≔ adjointify (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1) (rel 𝕎 A2 B2 x0 x1)
      (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1) (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_encode_decode A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_decode_encode A0 A1 A2 B0 B1 B2 x0 x1)

{` Next we prove that the codes are fibrant if the inputs are.  This is just putting together 𝕗Σ and 𝕗Π. `}

def 𝕗_𝕎_code (A0 A1 : Type) (A2 : Br Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type) (B2 : rel ((X ↦ X → Type) : Type → Type) A2 B0 B1)
  (𝕗A0 : isFibrant A0) (𝕗A1 : isFibrant A1)
  (𝕗A2 : rel isFibrant A2 𝕗A0 𝕗A1) (𝕗B0 : (a0 : A0) → isFibrant (B0 a0))
  (𝕗B1 : (a1 : A1) → isFibrant (B1 a1))
  (𝕗B2 : rel Π A2 {x ↦ isFibrant (B0 x)} {x ↦ isFibrant (B1 x)}
           (x ⤇ rel isFibrant (B2 x.2)) 𝕗B0 𝕗B1) (x0 : 𝕎 A0 B0)
  (x1 : 𝕎 A1 B1)
  : isFibrant (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
  ≔ match x0, x1 [
| sup. a0 f0, sup. a1 f1 ↦
    𝕗Σ (A2 a0 a1)
      (a2 ↦
       (b0 : B0 a0) (b1 : B1 a1) (b2 : B2 a2 b0 b1)
       → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1)) (𝕗A2 .id a0 a1)
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
             𝕗Π (B2 a2 b0 b1)
               (_ ↦ 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
               (𝕗B2 a2 .id b0 b1)
               (b2 ↦
                𝕗_𝕎_code A0 A1 A2 B0 B1 B2 𝕗A0 𝕗A1 𝕗A2 𝕗B0 𝕗B1 𝕗B2 (f0 b0)
                  (f1 b1)))))]

{` Finally, we can prove that W-types are fibrant.  Note that there are "recursive calls" to 𝕗𝕎 in *all* the clauses.  I'm not exactly sure how they are justified in the cases of tr and lift, but note that they are inside matches as well.  `}

def 𝕗𝕎 (A : Type) (B : A → Type) (𝕗A : isFibrant A)
  (𝕗B : (x : A) → isFibrant (B x))
  : isFibrant (𝕎 A B)
  ≔ [
| .trr.p ↦ [
  | sup. a0 f0 ↦
      sup. (𝕗A.2 .trr a0)
        (rel 𝕗Π (B.2 (𝕗A.2 .liftr a0)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
             (_ ⤇ rel 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 .liftr a0))
             {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
             (_ ⤇ rel 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2)
         .trr f0)]
| .trl.p ↦ [
  | sup. a1 f1 ↦
      sup. (𝕗A.2 .trl a1)
        (rel 𝕗Π (B.2 (𝕗A.2 .liftl a1)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
             (_ ⤇ rel 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 .liftl a1))
             {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
             (_ ⤇ rel 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2)
         .trl f1)]
| .liftr.p ↦ [
  | sup. a0 f0 ↦
      sup. (𝕗A.2 .liftr a0)
        (rel 𝕗Π (B.2 (𝕗A.2 .liftr a0)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
             (_ ⤇ rel 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 .liftr a0))
             {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
             (_ ⤇ rel 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2)
         .liftr f0)]
| .liftl.p ↦ [
  | sup. a1 f1 ↦
      sup. (𝕗A.2 .liftl a1)
        (rel 𝕗Π (B.2 (𝕗A.2 .liftl a1)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
             (_ ⤇ rel 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 .liftl a1))
             {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
             (_ ⤇ rel 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2)
         .liftl f1)]
| .id.p ↦ x0 x1 ↦
    𝕗eqv (𝕎_code A.0 A.1 A.2 B.0 B.1 B.2 x0 x1) (rel 𝕎 A.2 B.2 x0 x1)
      (Id_𝕎_iso A.0 A.1 A.2 B.0 B.1 B.2 x0 x1)
      (𝕗_𝕎_code A.0 A.1 A.2 B.0 B.1 B.2 𝕗A.0 𝕗A.1 𝕗A.2 𝕗B.0 𝕗B.1 𝕗B.2 x0 x1)]

{` The Id-types of a W-type can also be characterized by a W-type with non-uniform parameters. We can prove they are fibrant as there is no need to fibrantly replace them. `}

section Parametrized_W ≔

  def 𝕎_spec : Type ≔ sig (
    R : Type,
    A : R → Fib,
    B : (r : R) → A r .t → Fib,
    k : (r : R) (a : A r .t) → B r a .t → R )

  def 𝕎 (s : 𝕎_spec) (r : s .R) : Type ≔ data [
  | sup. (a : s .A r .t) (f : (b : s .B r a .t) → 𝕎 s (s .k r a b)) ]

  def 𝕎_proj1 (s : 𝕎_spec) (r : s .R) (x : 𝕎 s r) : s .A r .t ≔ match x [
  | sup. a f ↦ a]

  def 𝕎_proj2 (s : 𝕎_spec) (r : s .R) (x : 𝕎 s r)
    : (b : s .B r (𝕎_proj1 s r x) .t) → 𝕎 s (s .k r (𝕎_proj1 s r x) b)
    ≔ match x [ sup. a f ↦ f ]

  def 𝕎_code_spec (s0 s1 : 𝕎_spec) (s2 : Br 𝕎_spec s0 s1) : 𝕎_spec ≔ (
    R ≔ sig (
      r0 : s0 .R,
      r1 : s1 .R,
      r2 : s2 .R r0 r1,
      x0 : 𝕎 s0 r0,
      x1 : 𝕎 s1 r1 ),
    A ≔ r ↦
      Idd𝕗 (s0 .A (r .r0)) (s1 .A (r .r1)) (s2 .A (r .r2))
        (𝕎_proj1 s0 (r .r0) (r .x0)) (𝕎_proj1 s1 (r .r1) (r .x1)),
    B ≔ r a2 ↦
      Σ𝕗 (s0 .B (r .r0) (𝕎_proj1 s0 (r .r0) (r .x0)))
        (b0 ↦
         Σ𝕗 (s1 .B (r .r1) (𝕎_proj1 s1 (r .r1) (r .x1)))
           (b1 ↦
            Idd𝕗 (s0 .B (r .r0) (𝕎_proj1 s0 (r .r0) (r .x0)))
              (s1 .B (r .r1) (𝕎_proj1 s1 (r .r1) (r .x1)))
              (s2 .B (r .r2) a2) b0 b1)),
    k ≔ r a2 b ↦ (
      r0 ≔ s0 .k (r .r0) (𝕎_proj1 s0 (r .r0) (r .x0)) (b .0),
      r1 ≔ s1 .k (r .r1) (𝕎_proj1 s1 (r .r1) (r .x1)) (b .1 .0),
      r2 ≔ s2 .k (r .r2) a2 (b .1 .1),
      x0 ≔ 𝕎_proj2 s0 (r .r0) (r .x0) (b .0),
      x1 ≔ 𝕎_proj2 s1 (r .r1) (r .x1) (b .1 .0)))

  def 𝕎_encode (s0 s1 : 𝕎_spec) (s2 : Br 𝕎_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕎 s0 r0) (x1 : 𝕎 s1 r1)
    (x2 : Br 𝕎 s2 r2 x0 x1)
    : 𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
    ≔ match x2 [
  | sup. a f ⤇
      sup. a.2
        (b ↦
         𝕎_encode s0 s1 s2 (s0 .k r0 a.0 (b .0)) (s1 .k r1 a.1 (b .1 .0))
           (s2 .k r2 a.2 (b .1 .1)) (f.0 (b .0)) (f.1 (b .1 .0))
           (f.2 (b .1 .1)))]

  def 𝕎_decode (s0 s1 : 𝕎_spec) (s2 : Br 𝕎_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕎 s0 r0) (x1 : 𝕎 s1 r1)
    (y2 : 𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
    : Br 𝕎 s2 r2 x0 x1
    ≔ match x0, x1, y2 [
  | sup. a0 f0, sup. a1 f1, sup. a2 f2 ↦
      sup. a2
        (b ⤇
         𝕎_decode s0 s1 s2 (s0 .k r0 a0 b.0) (s1 .k r1 a1 b.1)
           (s2 .k r2 a2 b.2) (f0 b.0) (f1 b.1) (f2 (b.0, (b.1, b.2))))]

  def 𝕎_decode_encode (s0 s1 : 𝕎_spec) (s2 : Br 𝕎_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕎 s0 r0) (x1 : 𝕎 s1 r1)
    (x2 : Br 𝕎 s2 r2 x0 x1)
    : eq (Br 𝕎 s2 r2 x0 x1)
        (𝕎_decode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕎_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
    ≔ match x2 [
  | sup. a f ⤇
      eq.ap
        (rel Π (s2 .B r2 a.2 .t) {b0 ↦ 𝕎 s0 (s0 .k r0 a.0 b0)}
           {b1 ↦ 𝕎 s1 (s1 .k r1 a.1 b1)} (b ⤇ rel 𝕎 s2 (s2 .k r2 a.2 b.2))
           f.0 f.1) (Br 𝕎 s2 r2 (sup. a.0 f.0) (sup. a.1 f.1))
        (f2 ↦ sup. a.2 f2)
        (b ⤇
         𝕎_decode s0 s1 s2 (s0 .k r0 a.0 b.0) (s1 .k r1 a.1 b.1)
           (s2 .k r2 a.2 b.2) (f.0 b.0) (f.1 b.1)
           (𝕎_encode s0 s1 s2 (s0 .k r0 a.0 b.0) (s1 .k r1 a.1 b.1)
              (s2 .k r2 a.2 b.2) (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
        (funext_refl (s0 .B r0 a.0 .t) (s1 .B r1 a.1 .t) (s2 .B r2 a.2 .t)
           (b0 ↦ 𝕎 s0 (s0 .k r0 a.0 b0)) (b1 ↦ 𝕎 s1 (s1 .k r1 a.1 b1))
           (b ⤇ rel 𝕎 s2 (s2 .k r2 a.2 b.2)) f.0 f.1
           (b ⤇
            𝕎_decode s0 s1 s2 (s0 .k r0 a.0 b.0) (s1 .k r1 a.1 b.1)
              (s2 .k r2 a.2 b.2) (f.0 b.0) (f.1 b.1)
              (𝕎_encode s0 s1 s2 (s0 .k r0 a.0 b.0) (s1 .k r1 a.1 b.1)
                 (s2 .k r2 a.2 b.2) (f.0 b.0) (f.1 b.1) (f.2 b.2))) f.2
           (b0 b1 b2 ↦
            𝕎_decode_encode s0 s1 s2 (s0 .k r0 a.0 b0) (s1 .k r1 a.1 b1)
              (s2 .k r2 a.2 b2) (f.0 b0) (f.1 b1) (f.2 b2)))]

  def 𝕎_encode_decode (s0 s1 : 𝕎_spec) (s2 : Br 𝕎_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕎 s0 r0) (x1 : 𝕎 s1 r1)
    (y2 : 𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
    : eq (𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
        (𝕎_encode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕎_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
    ≔ match x0, x1, y2 [
  | sup. a0 f0, sup. a1 f1, sup. a2 f2 ↦
      eq.ap
        ((b2
         : 𝕎_code_spec s0 s1 s2
         .B (r0, r1, r2, sup. a0 f0, sup. a1 f1) a2
         .t)
         → 𝕎 (𝕎_code_spec s0 s1 s2)
             (𝕎_code_spec s0 s1 s2
              .k (r0, r1, r2, sup. a0 f0, sup. a1 f1) a2 b2))
        (𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)) (f2 ↦ sup. a2 f2)
        (b ↦
         𝕎_encode s0 s1 s2 (s0 .k r0 a0 (b .0)) (s1 .k r1 a1 (b .1 .0))
           (s2 .k r2 a2 (b .1 .1)) (f0 (b .0)) (f1 (b .1 .0))
           (𝕎_decode s0 s1 s2 (s0 .k r0 a0 (b .0)) (s1 .k r1 a1 (b .1 .0))
              (s2 .k r2 a2 (b .1 .1)) (f0 (b .0)) (f1 (b .1 .0)) (f2 b)))
        f2
        (funext
           (𝕎_code_spec s0 s1 s2
            .B (r0, r1, r2, sup. a0 f0, sup. a1 f1) a2
            .t)
           (b ↦
            𝕎 (𝕎_code_spec s0 s1 s2)
              (𝕎_code_spec s0 s1 s2
               .k (r0, r1, r2, sup. a0 f0, sup. a1 f1) a2 b))
           (b ↦
            𝕎_encode s0 s1 s2 (s0 .k r0 a0 (b .0)) (s1 .k r1 a1 (b .1 .0))
              (s2 .k r2 a2 (b .1 .1)) (f0 (b .0)) (f1 (b .1 .0))
              (𝕎_decode s0 s1 s2 (s0 .k r0 a0 (b .0))
                 (s1 .k r1 a1 (b .1 .0)) (s2 .k r2 a2 (b .1 .1))
                 (f0 (b .0)) (f1 (b .1 .0)) (f2 b))) f2
           (b ↦
            𝕎_encode_decode s0 s1 s2 (s0 .k r0 a0 (b .0))
              (s1 .k r1 a1 (b .1 .0)) (s2 .k r2 a2 (b .1 .1)) (f0 (b .0))
              (f1 (b .1 .0)) (f2 b)))]

  def Id_𝕎_iso (s0 s1 : 𝕎_spec) (s2 : Br 𝕎_spec s0 s1) (r0 : s0 .R)
    (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕎 s0 r0) (x1 : 𝕎 s1 r1)
    : 𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1) ≅ Br 𝕎 s2 r2 x0 x1
    ≔ adjointify (𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
        (Br 𝕎 s2 r2 x0 x1) (𝕎_decode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕎_encode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕎_encode_decode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕎_decode_encode s0 s1 s2 r0 r1 r2 x0 x1)

{` The same caveat holds here as in the proof that W-types are fibrant using the recursive characterization of Id-types. `}

  def 𝕗𝕎 (s : 𝕎_spec) (r : s .R) : isFibrant (𝕎 s r) ≔ [
  | .trr.p ↦ [
    | sup. a0 f0 ↦
        sup. (s.2 .A r.2 .f .trr a0)
          (rel 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftr a0) .t)
               {b0 ↦ 𝕎 s.0 (s.0 .k r.0 a0 b0)}
               {b1 ↦ 𝕎 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr a0) b1)}
               (b ⤇ rel 𝕎 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr a0) b.2))
               (s.2 .B r.2 (s.2 .A r.2 .f .liftr a0) .f)
               {b0 ↦ 𝕗𝕎 s.0 (s.0 .k r.0 a0 b0)}
               {b1 ↦ 𝕗𝕎 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr a0) b1)}
               (b ⤇ rel 𝕗𝕎 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr a0) b.2))
           .trr f0)]
  | .trl.p ↦ [
    | sup. a1 f1 ↦
        sup. (s.2 .A r.2 .f .trl a1)
          (rel 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftl a1) .t)
               {b0 ↦ 𝕎 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl a1) b0)}
               {b1 ↦ 𝕎 s.1 (s.1 .k r.1 a1 b1)}
               (b ⤇ rel 𝕎 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl a1) b.2))
               (s.2 .B r.2 (s.2 .A r.2 .f .liftl a1) .f)
               {b0 ↦ 𝕗𝕎 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl a1) b0)}
               {b1 ↦ 𝕗𝕎 s.1 (s.1 .k r.1 a1 b1)}
               (b ⤇ rel 𝕗𝕎 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl a1) b.2))
           .trl f1)]
  | .liftr.p ↦ [
    | sup. a0 f0 ↦
        sup. (s.2 .A r.2 .f .liftr a0)
          (rel 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftr a0) .t)
               {b0 ↦ 𝕎 s.0 (s.0 .k r.0 a0 b0)}
               {b1 ↦ 𝕎 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr a0) b1)}
               (b ⤇ rel 𝕎 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr a0) b.2))
               (s.2 .B r.2 (s.2 .A r.2 .f .liftr a0) .f)
               {b0 ↦ 𝕗𝕎 s.0 (s.0 .k r.0 a0 b0)}
               {b1 ↦ 𝕗𝕎 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr a0) b1)}
               (b ⤇ rel 𝕗𝕎 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr a0) b.2))
           .liftr f0)]
  | .liftl.p ↦ [
    | sup. a1 f1 ↦
        sup. (s.2 .A r.2 .f .liftl a1)
          (rel 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftl a1) .t)
               {b0 ↦ 𝕎 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl a1) b0)}
               {b1 ↦ 𝕎 s.1 (s.1 .k r.1 a1 b1)}
               (b ⤇ rel 𝕎 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl a1) b.2))
               (s.2 .B r.2 (s.2 .A r.2 .f .liftl a1) .f)
               {b0 ↦ 𝕗𝕎 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl a1) b0)}
               {b1 ↦ 𝕗𝕎 s.1 (s.1 .k r.1 a1 b1)}
               (b ⤇ rel 𝕗𝕎 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl a1) b.2))
           .liftl f1)]
  | .id.p ↦ x0 x1 ↦
      𝕗eqv (𝕎 (𝕎_code_spec s.0 s.1 s.2) (r.0, r.1, r.2, x0, x1))
        (Br 𝕎 s.2 r.2 x0 x1) (Id_𝕎_iso s.0 s.1 s.2 r.0 r.1 r.2 x0 x1)
        (𝕗𝕎 (𝕎_code_spec s.0 s.1 s.2) (r.0, r.1, r.2, x0, x1))]

end

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

def 𝕄_code_spec (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) : 𝕄_spec ≔ (
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

def 𝕄_encode (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x2 : rel 𝕄 s2 r2 x0 x1)
  : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
  ≔ [
| .recv ↦ x2 .recv
| .send ↦ b ↦
    𝕄_encode s0 s1 s2 (s0 .k r0 (x0 .recv) (b .0))
      (s1 .k r1 (x1 .recv) (b .1 .0)) (s2 .k r2 (x2 .recv) (b .1 .1))
      (x0 .send (b .0)) (x1 .send (b .1 .0)) (x2 .send (b .1 .1))]

def 𝕄_decode (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
  : rel 𝕄 s2 r2 x0 x1
  ≔ [
| .recv ↦ y2 .recv
| .send ↦ b ⤇
    𝕄_decode s0 s1 s2 (s0 .k r0 (x0 .recv) b.0) (s1 .k r1 (x1 .recv) b.1)
      (s2 .k r2 (y2 .recv) b.2) (x0 .send b.0) (x1 .send b.1)
      (y2 .send (b.0, (b.1, b.2)))]

{` We need "coinductive extensionality" for eq.  The version we need says that the eq-types of 𝕄, dependent over an equality of indices, are again an 𝕄-type, similar to the codes for Br but without changing the spec.  In the application we only use this over a fixed index, but we can't *define* it in general without passing to a non-rfl equality of indices. `}

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
        (ap3d (s .R) (r ↦ s .A r .t) (r a ↦ s .B r a .t) (s .R) (s .k) r0
           r1 r2 (x0 .recv) (x1 .recv) (x2 .recv) b0 b1 b2) (x0 .send b0)
        (x1 .send b1) ]

axiom 𝕄_ext (s : 𝕄_spec) (r : s .R) (x0 x1 : 𝕄 s r)
  (y2 : 𝕄_bisim s r r rfl. x0 x1)
  : eq (𝕄 s r) x0 x1

def 𝕄_encode_decode_bisim (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1)
  (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0)
  (x1 : 𝕄 s1 r1) (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
  : 𝕄_bisim (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
      (r0, r1, r2, x0, x1) rfl.
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
  ≔ [
| .recv ↦ rfl.
| .send ↦ b0 b1 b2 ↦ match b2 [
  | rfl. ↦
      𝕄_encode_decode_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) (b0 .0))
        (s1 .k r1 (x1 .recv) (b0 .1 .0)) (s2 .k r2 (y2 .recv) (b0 .1 .1))
        (x0 .send (b0 .0)) (x1 .send (b0 .1 .0)) (y2 .send b0)]]

def 𝕄_encode_decode (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
  : eq (𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
  ≔ 𝕄_ext (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
      (𝕄_encode_decode_bisim s0 s1 s2 r0 r1 r2 x0 x1 y2)

{` For the other direction we need a version of this for rel 𝕄. `}

def refl_𝕄_bisim (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r20 : s2 .R r0 r1) (r21 : s2 .R r0 r1)
  (r22 : eq (s2 .R r0 r1) r20 r21) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x20 : rel 𝕄 s2 r20 x0 x1) (x21 : rel 𝕄 s2 r21 x0 x1)
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
    → refl_𝕄_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) b0)
        (s1 .k r1 (x1 .recv) b1) (s2 .k r20 (x20 .recv) b20)
        (s2 .k r21 (x21 .recv) b21)
        (ap3d (s2 .R r0 r1) (r2 ↦ s2 .A r2 .t (x0 .recv) (x1 .recv))
           (r2 a2 ↦ s2 .B r2 a2 .t b0 b1)
           (s2 .R (s0 .k r0 (x0 .recv) b0) (s1 .k r1 (x1 .recv) b1))
           (r2 a2 b2 ↦ s2 .k r2 a2 b2) r20 r21 r22 (x20 .recv) (x21 .recv)
           (y2 .recv) b20 b21 b22) (x0 .send b0) (x1 .send b1)
        (x20 .send b20) (x21 .send b21) ]

axiom refl_𝕄_ext (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x20 : rel 𝕄 s2 r2 x0 x1) (x21 : rel 𝕄 s2 r2 x0 x1)
  (y22 : refl_𝕄_bisim s0 s1 s2 r0 r1 r2 r2 rfl. x0 x1 x20 x21)
  : eq (rel 𝕄 s2 r2 x0 x1) x20 x21

def 𝕄_decode_encode_bisim (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1)
  (r0 : s0 .R) (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0)
  (x1 : 𝕄 s1 r1) (x2 : rel 𝕄 s2 r2 x0 x1)
  : refl_𝕄_bisim s0 s1 s2 r0 r1 r2 r2 rfl. x0 x1
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
  ≔ [
| .recv ↦ rfl.
| .send ↦ b0 b1 b20 b21 b22 ↦ match b22 [
  | rfl. ↦
      𝕄_decode_encode_bisim s0 s1 s2 (s0 .k r0 (x0 .recv) b0)
        (s1 .k r1 (x1 .recv) b1) (s2 .k r2 (x2 .recv) b20) (x0 .send b0)
        (x1 .send b1) (x2 .send b20)]]

def 𝕄_decode_encode (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  (x2 : rel 𝕄 s2 r2 x0 x1)
  : eq (rel 𝕄 s2 r2 x0 x1)
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
  ≔ refl_𝕄_ext s0 s1 s2 r0 r1 r2 x0 x1
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
      (𝕄_decode_encode_bisim s0 s1 s2 r0 r1 r2 x0 x1 x2)

def Id_𝕄_iso (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 .R)
  (r1 : s1 .R) (r2 : s2 .R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1)
  : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1) ≅ rel 𝕄 s2 r2 x0 x1
  ≔ adjointify (𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
      (rel 𝕄 s2 r2 x0 x1) (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_encode_decode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_decode_encode s0 s1 s2 r0 r1 r2 x0 x1)

{` And finally we can prove that 𝕄-types are fibrant.  Again we have "recursive calls" to 𝕗𝕄 in each of the clauses, presumably justified by some kind of productivity. `}

def 𝕗𝕄 (s : 𝕄_spec) (r : s .R) : isFibrant (𝕄 s r) ≔ [
| .trr.p ↦ x0 ↦ [
  | .recv ↦ s.2 .A r.2 .f .trr (x0 .recv)
  | .send ↦
      rel 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftr (x0 .recv)) .t)
          {b0 ↦ 𝕄 s.0 (s.0 .k r.0 (x0 .recv) b0)}
          {b1 ↦ 𝕄 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr (x0 .recv)) b1)}
          (b ⤇ rel 𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr (x0 .recv)) b.2))
          (s.2 .B r.2 (s.2 .A r.2 .f .liftr (x0 .recv)) .f)
          {b0 ↦ 𝕗𝕄 s.0 (s.0 .k r.0 (x0 .recv) b0)}
          {b1 ↦ 𝕗𝕄 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr (x0 .recv)) b1)}
          (b ⤇
           rel 𝕗𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr (x0 .recv)) b.2))
        .trr (b0 ↦ x0 .send b0)]
| .trl.p ↦ x1 ↦ [
  | .recv ↦ s.2 .A r.2 .f .trl (x1 .recv)
  | .send ↦
      rel 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftl (x1 .recv)) .t)
          {b0 ↦ 𝕄 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl (x1 .recv)) b0)}
          {b1 ↦ 𝕄 s.1 (s.1 .k r.1 (x1 .recv) b1)}
          (b ⤇ rel 𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl (x1 .recv)) b.2))
          (s.2 .B r.2 (s.2 .A r.2 .f .liftl (x1 .recv)) .f)
          {b0 ↦ 𝕗𝕄 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl (x1 .recv)) b0)}
          {b1 ↦ 𝕗𝕄 s.1 (s.1 .k r.1 (x1 .recv) b1)}
          (b ⤇
           rel 𝕗𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl (x1 .recv)) b.2))
        .trl (b1 ↦ x1 .send b1)]
| .liftr.p ↦ x0 ↦ [
  | .recv ↦ s.2 .A r.2 .f .liftr (x0 .recv)
  | .send ↦
      rel 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftr (x0 .recv)) .t)
          {b0 ↦ 𝕄 s.0 (s.0 .k r.0 (x0 .recv) b0)}
          {b1 ↦ 𝕄 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr (x0 .recv)) b1)}
          (b ⤇ rel 𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr (x0 .recv)) b.2))
          (s.2 .B r.2 (s.2 .A r.2 .f .liftr (x0 .recv)) .f)
          {b0 ↦ 𝕗𝕄 s.0 (s.0 .k r.0 (x0 .recv) b0)}
          {b1 ↦ 𝕗𝕄 s.1 (s.1 .k r.1 (s.2 .A r.2 .f .trr (x0 .recv)) b1)}
          (b ⤇
           rel 𝕗𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftr (x0 .recv)) b.2))
        .liftr (b0 ↦ x0 .send b0)]
| .liftl.p ↦ x1 ↦ [
  | .recv ↦ s.2 .A r.2 .f .liftl (x1 .recv)
  | .send ↦
      rel 𝕗Π (s.2 .B r.2 (s.2 .A r.2 .f .liftl (x1 .recv)) .t)
          {b0 ↦ 𝕄 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl (x1 .recv)) b0)}
          {b1 ↦ 𝕄 s.1 (s.1 .k r.1 (x1 .recv) b1)}
          (b ⤇ rel 𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl (x1 .recv)) b.2))
          (s.2 .B r.2 (s.2 .A r.2 .f .liftl (x1 .recv)) .f)
          {b0 ↦ 𝕗𝕄 s.0 (s.0 .k r.0 (s.2 .A r.2 .f .trl (x1 .recv)) b0)}
          {b1 ↦ 𝕗𝕄 s.1 (s.1 .k r.1 (x1 .recv) b1)}
          (b ⤇
           rel 𝕗𝕄 s.2 (s.2 .k r.2 (s.2 .A r.2 .f .liftl (x1 .recv)) b.2))
        .liftl (b1 ↦ x1 .send b1)]
| .id.p ↦ x0 x1 ↦
    𝕗eqv (𝕄 (𝕄_code_spec s.0 s.1 s.2) (r.0, r.1, r.2, x0, x1))
      (rel 𝕄 s.2 r.2 x0 x1) (Id_𝕄_iso s.0 s.1 s.2 r.0 r.1 r.2 x0 x1)
      (𝕗𝕄 (𝕄_code_spec s.0 s.1 s.2) (r.0, r.1, r.2, x0, x1))]
