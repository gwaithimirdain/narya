{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

def isContr (A : Type) : Type ≔ sig (
  center : A,
  contract : (a : A) → Id A a center )

def iscontr_idfrom (A : Type) (a0 : A) : isContr (Σ A (a1 ↦ Id A a0 a1))
  ≔ (
  center ≔ (a0, refl a0),
  contract ≔ a1_a2 ↦
    let a1 ≔ a1_a2 .fst in
    let a2 ≔ a1_a2 .snd in
    (refl ((z ↦ Id A z a0) : A → Type) a2 .trr (refl a0),
     sym (refl ((z ↦ Id A z a0) : A → Type) a2 .liftr (refl a0))))

def is11 (A B : Type) (R : A → B → Type) : Type ≔ sig (
  contrr : (a : A) → isContr (Σ B (b ↦ R a b)),
  contrl : (b : B) → isContr (Σ A (a ↦ R a b)) )

{` A 1-1 correspondence induces another one on identity types.  This is where the real work of univalence lies. `}
def is11_Id (A0 A1 : Type) (A2 : Id Type A0 A1) (B0 B1 : Type)
  (B2 : Id Type B0 B1) (R0 : A0 → B0 → Type) (re0 : is11 A0 B0 R0)
  (R1 : A1 → B1 → Type) (re1 : is11 A1 B1 R1)
  (R2 : Id ((X Y ↦ (X → Y → Type)) : (X Y : Type) → Type) A2 B2 R0 R1)
  (re2 : refl is11 A2 B2 R2 re0 re1) (a0 : A0) (a1 : A1) (b0 : B0)
  (b1 : B1) (r0 : R0 a0 b0) (r1 : R1 a1 b1)
  : is11 (A2 a0 a1) (B2 b0 b1) (a2 b2 ↦ R2 a2 b2 r0 r1)
  ≔ (
  contrr ≔ a2 ↦
    let S : (y0 : B0) (y1 : B1) → R0 a0 y0 → R1 a1 y1 → Type
      ≔ y0 y1 z0 z1 ↦ Σ (B2 y0 y1) (y2 ↦ R2 a2 y2 z0 z1) in
    let b0' : B0 ≔ re0 .contrr a0 .center .fst in
    let b1' : B1 ≔ re1 .contrr a1 .center .fst in
    let r0' : R0 a0 b0' ≔ re0 .contrr a0 .center .snd in
    let r1' : R1 a1 b1' ≔ re1 .contrr a1 .center .snd in
    let u : S b0' b1' r0' r1' ≔ (
      re2 .contrr a2 .center .fst,
      re2 .contrr a2 .center .snd) in
    let p0 : Id B0 b0 b0' ≔ re0 .contrr a0 .contract (b0, r0) .fst in
    let p1 : Id B1 b1 b1' ≔ re1 .contrr a1 .contract (b1, r1) .fst in
    let q0 : Id (R0 a0) p0 r0 r0'
      ≔ re0 .contrr a0 .contract (b0, r0) .snd in
    let q1 : Id (R1 a1) p1 r1 r1'
      ≔ re1 .contrr a1 .contract (b1, r1) .snd in
    (refl S p0 p1 q0 q1 .trl u,
     v2 ↦
       let w
         ≔ re2
             .contrr a2
             .contract {(b0, r0)} {(b1, r1)} (v2 .fst, v2 .snd) in
       S⁽ᵉᵉ⁾ (sym (refl p0)) (sym (refl p1)) (sym (refl q0))
           (sym (refl q1)) {v2} {u} (sym w .fst, sym w .snd)
           (refl S p0 p1 q0 q1 .liftl u)
         .trl (refl u)),
  contrl ≔ b2 ↦
    let S : (x0 : A0) (x1 : A1) → R0 x0 b0 → R1 x1 b1 → Type
      ≔ x0 x1 z0 z1 ↦ Σ (A2 x0 x1) (x2 ↦ R2 x2 b2 z0 z1) in
    let a0' : A0 ≔ re0 .contrl b0 .center .fst in
    let a1' : A1 ≔ re1 .contrl b1 .center .fst in
    let r0' : R0 a0' b0 ≔ re0 .contrl b0 .center .snd in
    let r1' : R1 a1' b1 ≔ re1 .contrl b1 .center .snd in
    let u : S a0' a1' r0' r1' ≔ (
      re2 .contrl b2 .center .fst,
      re2 .contrl b2 .center .snd) in
    let p0 : Id A0 a0 a0' ≔ re0 .contrl b0 .contract (a0, r0) .fst in
    let p1 : Id A1 a1 a1' ≔ re1 .contrl b1 .contract (a1, r1) .fst in
    let q0 : Id R0 p0 (refl b0) r0 r0'
      ≔ re0 .contrl b0 .contract (a0, r0) .snd in
    let q1 : Id R1 p1 (refl b1) r1 r1'
      ≔ re1 .contrl b1 .contract (a1, r1) .snd in
    (refl S p0 p1 q0 q1 .trl u,
     v2 ↦
       let w
         ≔ re2
             .contrl b2
             .contract {(a0, r0)} {(a1, r1)} (v2 .fst, v2 .snd) in
       S⁽ᵉᵉ⁾ (sym (refl p0)) (sym (refl p1)) (sym (refl q0))
           (sym (refl q1)) {v2} {u} (sym w .fst, sym w .snd)
           (refl S p0 p1 q0 q1 .liftl u)
         .trl (refl u)))

{` Any 1-1 correspondence is a bisimulation, because 1-1 correspondences lift to identity types. `}
def bisim_of_11 (A B : Type) (R : A → B → Type) (re : is11 A B R)
  : isBisim A B R
  ≔ [
| .trr ↦ a ↦ re .contrr a .center .fst
| .liftr ↦ a ↦ re .contrr a .center .snd
| .trl ↦ b ↦ re .contrl b .center .fst
| .liftl ↦ b ↦ re .contrl b .center .snd
| .id.e ↦ a0 b0 r0 a1 b1 r1 ↦
    bisim_of_11 (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ (R.2 a2 b2 r0 r1))
      (is11_Id A.0 A.1 A.2 B.0 B.1 B.2 R.0 re.0 R.1 re.1 R.2 re.2 a0 a1 b0
         b1 r0 r1)]

def univalence (A B : Type) (f : A → B)
  (fe : (b : B) → isContr (Σ A (a ↦ Id B (f a) b)))
  : Id Type A B
  ≔ glue A B (a b ↦ Id B (f a) b)
      (bisim_of_11 A B (a b ↦ Id B (f a) b)
         (contrr ≔ a ↦ iscontr_idfrom B (f a), contrl ≔ fe))
