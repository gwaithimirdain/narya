option parametric ≔ arity 2, letter p, name rel Br

import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"

{` Univalence `}

{` We factor out the Gel bookkeeping and first prove a lemma assuming we already have something in "Id Type".  Something like this seems necessary for the coinductive hypothesis to be strong enough.  Proving this about bisimulations is the most straightforward version. `}
def pre_univalence (A : Fib) (B : Fib) (G : Br Type (A .t) (B .t))
  (𝕗G : (a : A .t) (b : B .t) → isFibrant (G a b))
  (re : isBisim A B (x y ↦ (G x y, 𝕗G x y)))
  : Br isFibrant G (A .f) (B .f)
  ≔ [
{` The 0-dimensional methods are just transport and lifting, which are part of the definition of a bisimulation. `}
| .trr.1 ↦ a ↦ re .trr a
| .trl.1 ↦ b ↦ re .trl b
| .liftr.1 ↦ a ↦ re .liftr a
| .liftl.1 ↦ b ↦ re .liftl b
{` This is just the assumption of pointwise fibrancy. `}
| .id.1 ↦ a b ↦ 𝕗G a b
{` The first few e-dimensional fields are uniform operations, which also follow from pointwise fibrancy. `}
| .trr.p ↦ {a0} {b0} r0 ↦ 𝕗G.2 (A.2 .f .liftr a0) (B.2 .f .liftr b0) .trr r0
| .trl.p ↦ {a1} {b1} r1 ↦ 𝕗G.2 (A.2 .f .liftl a1) (B.2 .f .liftl b1) .trl r1
| .liftr.p ↦ {a0} {b0} r0 ↦
    sym (𝕗G.2 (A.2 .f .liftr a0) (B.2 .f .liftr b0) .liftr r0)
| .liftl.p ↦ {a1} {b1} r1 ↦
    sym (𝕗G.2 (A.2 .f .liftl a1) (B.2 .f .liftl b1) .liftl r1)
{` Here is the most interesting bit, where we coinductively use the fact that bisimulations are defined to lift to identity types.  We have to transfer it across a symmetry equivalence. `}
| .id.p ↦ {a0} {b0} r0 {a1} {b1} r1 ↦
    let s
      : (a2 : A.2 .t a0 a1) (b2 : B.2 .t b0 b1)
        → G.2 a2 b2 r0 r1 ≅ sym G.2 r0 r1 a2 b2
      ≔ a2 b2 ↦
        sym_eqv (A.0 .t) (A.1 .t) (A.2 .t) (B.0 .t) (B.1 .t) (B.2 .t) G.0
          G.1 G.2 a0 a1 a2 b0 b1 b2 r0 r1 in
    let 𝕗sG
      : (a2 : A.2 .t a0 a1) (b2 : B.2 .t b0 b1)
        → isFibrant (sym G.2 r0 r1 a2 b2)
      ≔ a2 b2 ↦
        𝕗eqv (G.2 a2 b2 r0 r1) (sym G.2 r0 r1 a2 b2) (s a2 b2)
          (𝕗G.2 a2 b2 .id r0 r1) in
    pre_univalence (Idd𝕗 A.0 A.1 A.2 a0 a1) (Idd𝕗 B.0 B.1 B.2 b0 b1)
      (sym G.2 r0 r1) 𝕗sG
      (isbisim_eqv (Idd𝕗 A.0 A.1 A.2 a0 a1) (Idd𝕗 B.0 B.1 B.2 b0 b1)
         (a2 b2 ↦ (G.2 a2 b2 r0 r1, 𝕗G.2 a2 b2 .id r0 r1))
         (a2 b2 ↦ (sym G.2 r0 r1 a2 b2, 𝕗sG a2 b2)) s
         (re.2 .id a0 b0 r0 a1 b1 r1))]

{` Now we put this together with Gel to prove univalence for fibrant types, which we can express for bisimulations or for 1-1 correspondences. `}
def univalence_bisim (A B : Fib) (R : A .t → B .t → Fib)
  (re : isBisim A B R)
  : Br Fib A B
  ≔
  let Rt : A .t → B .t → Type ≔ x y ↦ R x y .t in
  let Rf : (a : A .t) (b : B .t) → isFibrant (Rt a b) ≔ x y ↦ R x y .f in
  (Gel (A .t) (B .t) Rt,
   pre_univalence A B (Gel (A .t) (B .t) Rt)
     (a b ↦ 𝕗Gel (A .t) (B .t) Rt Rf a b)
     (isbisim_eqv A B (x y ↦ R x y)
        (a b ↦ (Gel (A .t) (B .t) Rt a b, 𝕗Gel (A .t) (B .t) Rt Rf a b))
        (a b ↦ Gel_iso (A .t) (B .t) Rt a b) re))

def univalence_11 (A B : Fib) (R : A .t → B .t → Fib) (re : is11 A B R)
  : Br Fib A B
  ≔ univalence_bisim A B R (bisim_of_11 A B R re)

{` Reflexivity of a type is a self-equivalence, but we don't have regularity, so its transports don't reduce to the identity.  However, with univalence we can build an alternative "strict reflexivity" that does. `}

def is11_Id𝕗 (A : Fib) : is11 A A (Id𝕗 A) ≔ (
  contrr ≔ iscontr_idfrom A,
  contrl ≔ iscontr_idto A)

def srefl (A : Fib) : Br Fib A A ≔ univalence_11 A A (Id𝕗 A) (is11_Id𝕗 A)

def srefl_is_strict (A : Fib) (a : A .t) : Br (A .t) (srefl A .f .trr a) a
  ≔ rel a

{` More generally, given any Voevodsky equivalence we can easily make it into a 1-1 correspondence and hence an identification. `}

def univalence_vv (A B : Fib) (f : A .t → B .t)
  (fe : (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b)))
  : Br Fib A B
  ≔ univalence_11 A B (a b ↦ Id𝕗 B (f a) b)
      (contrr ≔ a ↦ iscontr_idfrom B (f a), contrl ≔ fe)

{` This is "definitional univalence": we can extract both the function and its inverse definitionally. `}

def univalence_is_left_definitional (A B : Fib) (f : A .t → B .t)
  (fe : (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b))) (a : A .t)
  : let E : Br Fib A B ≔ univalence_vv A B f fe in
    Br (B .t) (E .f .trr a) (f a)
  ≔ rel (f a)

def univalence_is_right_definitional (A B : Fib) (f : A .t → B .t)
  (fe : (b : B .t) → isContr (Σ𝕗 A (a ↦ Id𝕗 B (f a) b))) (b : B .t)
  : let E : Br Fib A B ≔ univalence_vv A B f fe in
    Br (A .t) (E .f .trl b) (fe b .center .fst)
  ≔ rel (fe b .center .fst)
