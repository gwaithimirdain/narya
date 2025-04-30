import "isfibrant"
import "bookhott"
import "hott_bookhott"
import "fibrant_types"
import "homotopy"
import "univalence"

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` We prove a version of univalence for 2-dimensional (i.e. ee-dimensional) squares.  Its input is a 2D correspondence that is a "2-dimensional bisimulation" in the following sence. `}

def isBisim_ee (A00 A01 : Fib) (A02 : Id Fib A00 A01) (A10 A11 : Fib)
  (A12 : Id Fib A10 A11) (A20 : Id Fib A00 A10) (A21 : Id Fib A01 A11)
  (A22 : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
         (a11 : A11 .t) (a12 : A12 .t a10 a11) (a20 : A20 .t a00 a10)
         (a21 : A21 .t a01 a11)
         → Fib)
  : Type
  ≔ codata [
| x .lr
  : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
    (a11 : A11 .t) (a12 : A12 .t a10 a11)
    → isBisim (Idd𝕗 A00 A10 A20 a00 a10) (Idd𝕗 A01 A11 A21 a01 a11)
        (a20 a21 ↦ A22 a00 a01 a02 a10 a11 a12 a20 a21)
| x .tb
  : (a00 : A00 .t) (a01 : A01 .t) (a10 : A10 .t) (a11 : A11 .t)
    (a20 : A20 .t a00 a10) (a21 : A21 .t a01 a11)
    → isBisim (Idd𝕗 A00 A01 A02 a00 a01) (Idd𝕗 A10 A11 A12 a10 a11)
        (a02 a12 ↦ A22 a00 a01 a02 a10 a11 a12 a20 a21)
| x .id.e
  : (a00 : A00.0 .t) (a01 : A01.0 .t) (a02 : A02.0 .t a00 a01)
    (a10 : A10.0 .t) (a11 : A11.0 .t) (a12 : A12.0 .t a10 a11)
    (a20 : A20.0 .t a00 a10) (a21 : A21.0 .t a01 a11)
    (a22 : A22.0 a00 a01 a02 a10 a11 a12 a20 a21 .t) (b00 : A00.1 .t)
    (b01 : A01.1 .t) (b02 : A02.1 .t b00 b01) (b10 : A10.1 .t)
    (b11 : A11.1 .t) (b12 : A12.1 .t b10 b11) (b20 : A20.1 .t b00 b10)
    (b21 : A21.1 .t b01 b11) (b22 : A22.1 b00 b01 b02 b10 b11 b12 b20 b21 .t)
    → isBisim_ee (Idd𝕗 A00.0 A00.1 A00.2 a00 b00)
        (Idd𝕗 A01.0 A01.1 A01.2 a01 b01)
        (refl Idd𝕗 A02.0 A02.1 (sym A02.2) a02 b02)
        (Idd𝕗 A10.0 A10.1 A10.2 a10 b10) (Idd𝕗 A11.0 A11.1 A11.2 a11 b11)
        (refl Idd𝕗 A12.0 A12.1 (sym A12.2) a12 b12)
        (refl Idd𝕗 A20.0 A20.1 (sym A20.2) a20 b20)
        (refl Idd𝕗 A21.0 A21.1 (sym A21.2) a21 b21)
        (c00 c01 c02 c10 c11 c12 c20 c21 ↦
         (A22.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21)
            .t a22 b22,
          A22.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21)
            .f
            .id.1 a22 b22)) ]

def isbisim_ee_eqv (A00 A01 : Fib) (A02 : Id Fib A00 A01) (A10 A11 : Fib)
  (A12 : Id Fib A10 A11) (A20 : Id Fib A00 A10) (A21 : Id Fib A01 A11)
  (A22 A22' : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01)
              (a10 : A10 .t) (a11 : A11 .t) (a12 : A12 .t a10 a11)
              (a20 : A20 .t a00 a10) (a21 : A21 .t a01 a11)
              → Fib)
  (e : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
       (a11 : A11 .t) (a12 : A12 .t a10 a11) (a20 : A20 .t a00 a10)
       (a21 : A21 .t a01 a11)
       → A22 a00 a01 a02 a10 a11 a12 a20 a21 .t
         ≅ A22' a00 a01 a02 a10 a11 a12 a20 a21 .t)
  (re : isBisim_ee A00 A01 A02 A10 A11 A12 A20 A21 A22)
  : isBisim_ee A00 A01 A02 A10 A11 A12 A20 A21 A22'
  ≔ [
| .lr ↦ a00 a01 a02 a10 a11 a12 ↦
    isbisim_eqv (Idd𝕗 A00 A10 A20 a00 a10) (Idd𝕗 A01 A11 A21 a01 a11)
      (a20 a21 ↦ A22 a00 a01 a02 a10 a11 a12 a20 a21)
      (a20 a21 ↦ A22' a00 a01 a02 a10 a11 a12 a20 a21)
      (a20 a21 ↦ e a00 a01 a02 a10 a11 a12 a20 a21)
      (re .lr a00 a01 a02 a10 a11 a12)
| .tb ↦ a00 a01 a10 a11 a20 a21 ↦
    isbisim_eqv (Idd𝕗 A00 A01 A02 a00 a01) (Idd𝕗 A10 A11 A12 a10 a11)
      (a02 a12 ↦ A22 a00 a01 a02 a10 a11 a12 a20 a21)
      (a02 a12 ↦ A22' a00 a01 a02 a10 a11 a12 a20 a21)
      (a02 a12 ↦ e a00 a01 a02 a10 a11 a12 a20 a21)
      (re .tb a00 a01 a10 a11 a20 a21)
| .id.e ↦
  a00 a01 a02 a10 a11 a12 a20 a21 a22 b00 b01 b02 b10 b11 b12 b20 b21 b22 ↦
    isbisim_ee_eqv (Idd𝕗 A00.0 A00.1 A00.2 a00 b00)
      (Idd𝕗 A01.0 A01.1 A01.2 a01 b01)
      (refl Idd𝕗 A02.0 A02.1 (sym A02.2) a02 b02)
      (Idd𝕗 A10.0 A10.1 A10.2 a10 b10) (Idd𝕗 A11.0 A11.1 A11.2 a11 b11)
      (refl Idd𝕗 A12.0 A12.1 (sym A12.2) a12 b12)
      (refl Idd𝕗 A20.0 A20.1 (sym A20.2) a20 b20)
      (refl Idd𝕗 A21.0 A21.1 (sym A21.2) a21 b21)
      (c00 c01 c02 c10 c11 c12 c20 c21 ↦
       (A22.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21)
          .t (e.0 a00 a01 a02 a10 a11 a12 a20 a21 .fro a22)
            (e.1 b00 b01 b02 b10 b11 b12 b20 b21 .fro b22),
        A22.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21)
          .f
          .id.1 (e.0 a00 a01 a02 a10 a11 a12 a20 a21 .fro a22)
            (e.1 b00 b01 b02 b10 b11 b12 b20 b21 .fro b22)))
      (c00 c01 c02 c10 c11 c12 c20 c21 ↦
       (A22'.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21)
          .t a22 b22,
        A22'.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21)
          .f
          .id.1 a22 b22))
      (c00 c01 c02 c10 c11 c12 c20 c21 ↦
       Id_eqv (A22.0 a00 a01 a02 a10 a11 a12 a20 a21 .t)
         (A22.1 b00 b01 b02 b10 b11 b12 b20 b21 .t)
         (A22.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21) .t)
         (A22'.0 a00 a01 a02 a10 a11 a12 a20 a21 .t)
         (A22'.1 b00 b01 b02 b10 b11 b12 b20 b21 .t)
         (A22'.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21) .t)
         (e.0 a00 a01 a02 a10 a11 a12 a20 a21)
         (e.1 b00 b01 b02 b10 b11 b12 b20 b21)
         (e.2 c00 c01 (sym c02) c10 c11 (sym c12) (sym c20) (sym c21)) a22
         b22)
      (re.2 .id.1 a00 a01 a02 a10 a11 a12 a20 a21
         (e.0 a00 a01 a02 a10 a11 a12 a20 a21 .fro a22) b00 b01 b02 b10 b11
         b12 b20 b21 (e.1 b00 b01 b02 b10 b11 b12 b20 b21 .fro b22))]

def pre_univalence_ee (A00 A01 : Fib) (A02 : Id Fib A00 A01) (A10 A11 : Fib)
  (A12 : Id Fib A10 A11) (A20 : Id Fib A00 A10) (A21 : Id Fib A01 A11)
  (A22 : Type⁽ᵉᵉ⁾ (A02 .t) (A12 .t) (A20 .t) (A21 .t))
  (𝕗A22 : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
          (a11 : A11 .t) (a12 : A12 .t a10 a11) (a20 : A20 .t a00 a10)
          (a21 : A21 .t a01 a11)
          → isFibrant (A22 a02 a12 a20 a21))
  (re : isBisim_ee A00 A01 A02 A10 A11 A12 A20 A21
          (a00 a01 a02 a10 a11 a12 a20 a21 ↦
           (A22 a02 a12 a20 a21, 𝕗A22 a00 a01 a02 a10 a11 a12 a20 a21)))
  : isFibrant⁽ᵉᵉ⁾ A22 (A02 .f) (A12 .f) (A20 .f) (A21 .f)
  ≔ [
{` The first group of methods are uniform transport and lifting, which we can obtain by lifting on the boundaries and box-filling. `}
| .trr.1 ↦ a0 ⤇
    re
      .tb a0.0 a0.1 (A20 .f .trr.1 a0.0) (A21 .f .trr.1 a0.1)
        (A20 .f .liftr.1 a0.0) (A21 .f .liftr.1 a0.1)
      .trr a0.2
| .liftr.1 ↦ a0 ⤇
    re
      .tb a0.0 a0.1 (A20 .f .trr.1 a0.0) (A21 .f .trr.1 a0.1)
        (A20 .f .liftr.1 a0.0) (A21 .f .liftr.1 a0.1)
      .liftr a0.2
| .trr.2 ↦ a0 ⤇
    re
      .lr a0.0 (A02 .f .trr.1 a0.0) (A02 .f .liftr.1 a0.0) a0.1
        (A12 .f .trr.1 a0.1) (A12 .f .liftr.1 a0.1)
      .trr a0.2
| .liftr.2 ↦ a0 ⤇
    sym
      (re
       .lr a0.0 (A02 .f .trr.1 a0.0) (A02 .f .liftr.1 a0.0) a0.1
         (A12 .f .trr.1 a0.1) (A12 .f .liftr.1 a0.1)
       .liftr a0.2)
| .trl.1 ↦ a1 ⤇
    re
      .tb (A20 .f .trl.1 a1.0) (A21 .f .trl.1 a1.1) a1.0 a1.1
        (A20 .f .liftl.1 a1.0) (A21 .f .liftl.1 a1.1)
      .trl a1.2
| .liftl.1 ↦ a1 ⤇
    re
      .tb (A20 .f .trl.1 a1.0) (A21 .f .trl.1 a1.1) a1.0 a1.1
        (A20 .f .liftl.1 a1.0) (A21 .f .liftl.1 a1.1)
      .liftl a1.2
| .trl.2 ↦ a1 ⤇
    re
      .lr (A02 .f .trl.1 a1.0) a1.0 (A02 .f .liftl.1 a1.0)
        (A12 .f .trl.1 a1.1) a1.1 (A12 .f .liftl.1 a1.1)
      .trl a1.2
| .liftl.2 ↦ a1 ⤇
    sym
      (re
       .lr (A02 .f .trl.1 a1.0) a1.0 (A02 .f .liftl.1 a1.0)
         (A12 .f .trl.1 a1.1) a1.1 (A12 .f .liftl.1 a1.1)
       .liftl a1.2)
{` The second group of methods just follow from fibrancy. `}
| .trr.e ↦ a ⤇
    𝕗A22.2 (A00.2 .f .liftr.1 a.00) (A01.2 .f .liftr.1 a.01)
        (sym (sym A02.2 .f .liftr.1 a.02)) (A10.2 .f .liftr.1 a.10)
        (A11.2 .f .liftr.1 a.11) (sym (sym A12.2 .f .liftr.1 a.12))
        (sym (sym A20.2 .f .liftr.1 a.20)) (sym (sym A21.2 .f .liftr.1 a.21))
      .trr.1 a.22
| .liftr.e ↦ a ⤇
    (𝕗A22.2 (A00.2 .f .liftr.1 a.00) (A01.2 .f .liftr.1 a.01)
         (sym (sym A02.2 .f .liftr.1 a.02)) (A10.2 .f .liftr.1 a.10)
         (A11.2 .f .liftr.1 a.11) (sym (sym A12.2 .f .liftr.1 a.12))
         (sym (sym A20.2 .f .liftr.1 a.20))
         (sym (sym A21.2 .f .liftr.1 a.21))
     .liftr.1 a.22)⁽³¹²⁾
| .trl.e ↦ a ⤇
    𝕗A22.2 (A00.2 .f .liftl.1 a.00) (A01.2 .f .liftl.1 a.01)
        (sym (sym A02.2 .f .liftl.1 a.02)) (A10.2 .f .liftl.1 a.10)
        (A11.2 .f .liftl.1 a.11) (sym (sym A12.2 .f .liftl.1 a.12))
        (sym (sym A20.2 .f .liftl.1 a.20)) (sym (sym A21.2 .f .liftl.1 a.21))
      .trl.1 a.22
| .liftl.e ↦ a ⤇
    (𝕗A22.2 (A00.2 .f .liftl.1 a.00) (A01.2 .f .liftl.1 a.01)
         (sym (sym A02.2 .f .liftl.1 a.02)) (A10.2 .f .liftl.1 a.10)
         (A11.2 .f .liftl.1 a.11) (sym (sym A12.2 .f .liftl.1 a.12))
         (sym (sym A20.2 .f .liftl.1 a.20))
         (sym (sym A21.2 .f .liftl.1 a.21))
     .liftl.1 a.22)⁽³¹²⁾
{` Now the two principal methods that are represented directly by the isBisim_ee methods 'lr' and 'tb'. `}
| .id.1 ↦ a0 a1 ⤇
    pre_univalence (Idd𝕗 A00 A10 A20 a0.0 a1.0) (Idd𝕗 A01 A11 A21 a0.1 a1.1)
      (A22 a0.2 a1.2) (a20 a21 ↦ 𝕗A22 a0.0 a0.1 a0.2 a1.0 a1.1 a1.2 a20 a21)
      (re .lr a0.0 a0.1 a0.2 a1.0 a1.1 a1.2)
| .id.2 ↦ a0 a1 ⤇
    pre_univalence (Idd𝕗 A00 A01 A02 a0.0 a1.0) (Idd𝕗 A10 A11 A12 a0.1 a1.1)
      (sym A22 a0.2 a1.2)
      (a20 a21 ↦
       𝕗eqv (A22 a20 a21 a0.2 a1.2) (sym A22 a0.2 a1.2 a20 a21)
         (sym_eqv (A00 .t) (A01 .t) (A02 .t) (A10 .t) (A11 .t) (A12 .t)
            (A20 .t) (A21 .t) A22 a0.0 a1.0 a20 a0.1 a1.1 a21 a0.2 a1.2)
         (𝕗A22 a0.0 a1.0 a20 a0.1 a1.1 a21 a0.2 a1.2))
      (isbisim_eqv (Idd𝕗 A00 A01 A02 a0.0 a1.0) (Idd𝕗 A10 A11 A12 a0.1 a1.1)
         (a02 a12 ↦
          (A22 a02 a12 a0.2 a1.2, 𝕗A22 a0.0 a1.0 a02 a0.1 a1.1 a12 a0.2 a1.2))
         (x y ↦
          (sym A22 a0.2 a1.2 x y,
           𝕗eqv (A22 x y a0.2 a1.2) (sym A22 a0.2 a1.2 x y)
             (sym_eqv (A00 .t) (A01 .t) (A02 .t) (A10 .t) (A11 .t) (A12 .t)
                (A20 .t) (A21 .t) A22 a0.0 a1.0 x a0.1 a1.1 y a0.2 a1.2)
             (𝕗A22 a0.0 a1.0 x a0.1 a1.1 y a0.2 a1.2)))
         (a20 a21 ↦
          sym_eqv (A00 .t) (A01 .t) (A02 .t) (A10 .t) (A11 .t) (A12 .t)
            (A20 .t) (A21 .t) A22 a0.0 a1.0 a20 a0.1 a1.1 a21 a0.2 a1.2)
         (re .tb a0.0 a1.0 a0.1 a1.1 a0.2 a1.2))
{` Finally, the coinductive case that follows by corecursion. `}
| .id.e ↦ a0 a1 ⤇
    let e312
      ≔ 312_eqv (A00.0 .t) (A00.1 .t) (A00.2 .t) (A01.0 .t) (A01.1 .t)
          (A01.2 .t) (A02.0 .t) (A02.1 .t) (A02.2 .t) (A10.0 .t) (A10.1 .t)
          (A10.2 .t) (A11.0 .t) (A11.1 .t) (A11.2 .t) (A12.0 .t) (A12.1 .t)
          (A12.2 .t) (A20.0 .t) (A20.1 .t) (A20.2 .t) (A21.0 .t) (A21.1 .t)
          (A21.2 .t) A22.0 A22.1 A22.2 in
    pre_univalence_ee (Idd𝕗 A00.0 A00.1 A00.2 a0.00 a1.00)
      (Idd𝕗 A01.0 A01.1 A01.2 a0.01 a1.01)
      (refl Idd𝕗 A02.0 A02.1 (sym A02.2) a0.02 a1.02)
      (Idd𝕗 A10.0 A10.1 A10.2 a0.10 a1.10)
      (Idd𝕗 A11.0 A11.1 A11.2 a0.11 a1.11)
      (refl Idd𝕗 A12.0 A12.1 (sym A12.2) a0.12 a1.12)
      (refl Idd𝕗 A20.0 A20.1 (sym A20.2) a0.20 a1.20)
      (refl Idd𝕗 A21.0 A21.1 (sym A21.2) a0.21 a1.21)
      (A22.2⁽³¹²⁾ a0.22 a1.22)
      (a200 a201 a202 a210 a211 a212 a220 a221 ↦
       𝕗eqv (A22.2 (sym a202) (sym a212) (sym a220) (sym a221) a0.22 a1.22)
         (A22.2⁽³¹²⁾ a0.22 a1.22 a202 a212 a220 a221)
         (e312 (a0.00) (a1.00) (a200) (a0.01) (a1.01) (a201) (a0.02) (a1.02)
            (sym a202) (a0.10) (a1.10) (a210) (a0.11) (a1.11) (a211) (a0.12)
            (a1.12) (sym a212) (a0.20) (a1.20) (sym a220) (a0.21) (a1.21)
            (sym a221) a0.22 a1.22)
         (𝕗A22.2 a200 a201 (sym a202) a210 a211 (sym a212) (sym a220)
              (sym a221)
          .id.1 a0.22 a1.22))
      (isbisim_ee_eqv (Idd𝕗 A00.0 A00.1 A00.2 a0.00 a1.00)
         (Idd𝕗 A01.0 A01.1 A01.2 a0.01 a1.01)
         (refl Idd𝕗 A02.0 A02.1 (sym A02.2) a0.02 a1.02)
         (Idd𝕗 A10.0 A10.1 A10.2 a0.10 a1.10)
         (Idd𝕗 A11.0 A11.1 A11.2 a0.11 a1.11)
         (refl Idd𝕗 A12.0 A12.1 (sym A12.2) a0.12 a1.12)
         (refl Idd𝕗 A20.0 A20.1 (sym A20.2) a0.20 a1.20)
         (refl Idd𝕗 A21.0 A21.1 (sym A21.2) a0.21 a1.21)
         (a200 a201 a202 a210 a211 a212 a220 a221 ↦
          (A22.2 (sym a202) (sym a212) (sym a220) (sym a221) a0.22 a1.22,
           𝕗A22.2 a200 a201 (sym a202) a210 a211 (sym a212) (sym a220)
               (sym a221)
             .id.1 a0.22 a1.22))
         (a00 a01 a02 a10 a11 a12 a20 a21 ↦
          (A22.2⁽³¹²⁾ a0.22 a1.22 a02 a12 a20 a21,
           𝕗eqv (A22.2 (sym a02) (sym a12) (sym a20) (sym a21) a0.22 a1.22)
             (A22.2⁽³¹²⁾ a0.22 a1.22 a02 a12 a20 a21)
             (e312 a0.00 a1.00 a00 a0.01 a1.01 a01 a0.02 a1.02 (sym a02)
                a0.10 a1.10 a10 a0.11 a1.11 a11 a0.12 a1.12 (sym a12) a0.20
                a1.20 (sym a20) a0.21 a1.21 (sym a21) a0.22 a1.22)
             (𝕗A22.2 a00 a01 (sym a02) a10 a11 (sym a12) (sym a20) (sym a21)
              .id.1 a0.22 a1.22)))
         (a00 a01 a02 a10 a11 a12 a20 a21 ↦
          (e312 a0.00 a1.00 a00 a0.01 a1.01 a01 a0.02 a1.02 (sym a02) a0.10
             a1.10 a10 a0.11 a1.11 a11 a0.12 a1.12 (sym a12) a0.20 a1.20
             (sym a20) a0.21 a1.21 (sym a21) a0.22 a1.22))
         (re.2 .id.1 a0.00 a0.01 a0.02 a0.10 a0.11 a0.12 a0.20 a0.21 a0.22
            a1.00 a1.01 a1.02 a1.10 a1.11 a1.12 a1.20 a1.21 a1.22))]

{` Of course, we need a 2-dimensional version of Gel. `}

def Gel_ee (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (R : (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10) (a11 : A11)
       (a12 : A12 a10 a11) (a20 : A20 a00 a10) (a21 : A21 a01 a11)
       → Type)
  : Type⁽ᵉᵉ⁾ A02 A12 A20 A21
  ≔ sig a00 a01 a02 a10 a11 a12 a20 a21 ↦ (
  ungel : R a00 a01 a02 a10 a11 a12 a20 a21 )

def Gel_ee_iso (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (R : (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10) (a11 : A11)
       (a12 : A12 a10 a11) (a20 : A20 a00 a10) (a21 : A21 a01 a11)
       → Type) (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10)
  (a11 : A11) (a12 : A12 a10 a11) (a20 : A20 a00 a10) (a21 : A21 a01 a11)
  : R a00 a01 a02 a10 a11 a12 a20 a21
    ≅ Gel_ee A00 A01 A02 A10 A11 A12 A20 A21 R a02 a12 a20 a21
  ≔ (
  to ≔ r ↦ (r,),
  fro ≔ r ↦ r .0,
  fro_to ≔ _ ↦ rfl.,
  to_fro ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 𝕗Gel_ee (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (R : (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10) (a11 : A11)
       (a12 : A12 a10 a11) (a20 : A20 a00 a10) (a21 : A21 a01 a11)
       → Type)
  (𝕗R : (a00 : A00) (a01 : A01) (a02 : A02 a00 a01) (a10 : A10) (a11 : A11)
        (a12 : A12 a10 a11) (a20 : A20 a00 a10) (a21 : A21 a01 a11)
        → isFibrant (R a00 a01 a02 a10 a11 a12 a20 a21)) (a00 : A00)
  (a01 : A01) (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
  (a20 : A20 a00 a10) (a21 : A21 a01 a11)
  : isFibrant (Gel_ee A00 A01 A02 A10 A11 A12 A20 A21 R a02 a12 a20 a21)
  ≔ 𝕗eqv (R a00 a01 a02 a10 a11 a12 a20 a21)
      (Gel_ee A00 A01 A02 A10 A11 A12 A20 A21 R a02 a12 a20 a21)
      (Gel_ee_iso A00 A01 A02 A10 A11 A12 A20 A21 R a00 a01 a02 a10 a11 a12
         a20 a21) (𝕗R a00 a01 a02 a10 a11 a12 a20 a21)

def univalence_ee (A00 A01 : Fib) (A02 : Id Fib A00 A01) (A10 A11 : Fib)
  (A12 : Id Fib A10 A11) (A20 : Id Fib A00 A10) (A21 : Id Fib A01 A11)
  (R : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
       (a11 : A11 .t) (a12 : A12 .t a10 a11) (a20 : A20 .t a00 a10)
       (a21 : A21 .t a01 a11)
       → Fib) (re : isBisim_ee A00 A01 A02 A10 A11 A12 A20 A21 R)
  : Fib⁽ᵉᵉ⁾ A02 A12 A20 A21
  ≔
  let Rt
    : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
      (a11 : A11 .t) (a12 : A12 .t a10 a11) (a20 : A20 .t a00 a10)
      (a21 : A21 .t a01 a11)
      → Type
    ≔ (a00 a01 a02 a10 a11 a12 a20 a21 ↦ R a00 a01 a02 a10 a11 a12 a20 a21 .t)
    in
  let Rf
    : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
      (a11 : A11 .t) (a12 : A12 .t a10 a11) (a20 : A20 .t a00 a10)
      (a21 : A21 .t a01 a11)
      → isFibrant (Rt a00 a01 a02 a10 a11 a12 a20 a21)
    ≔ (a00 a01 a02 a10 a11 a12 a20 a21 ↦ R a00 a01 a02 a10 a11 a12 a20 a21 .f)
    in
  let Gt
    ≔ Gel_ee (A00 .t) (A01 .t) (A02 .t) (A10 .t) (A11 .t) (A12 .t) (A20 .t)
        (A21 .t) Rt in
  let Gf
    : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
      (a11 : A11 .t) (a12 : A12 .t a10 a11) (a20 : A20 .t a00 a10)
      (a21 : A21 .t a01 a11)
      → isFibrant (Gt a02 a12 a20 a21)
    ≔ (a00 a01 a02 a10 a11 a12 a20 a21 ↦
       𝕗Gel_ee (A00 .t) (A01 .t) (A02 .t) (A10 .t) (A11 .t) (A12 .t) (A20 .t)
         (A21 .t) Rt Rf a00 a01 a02 a10 a11 a12 a20 a21) in
  let G
    : (a00 : A00 .t) (a01 : A01 .t) (a02 : A02 .t a00 a01) (a10 : A10 .t)
      (a11 : A11 .t) (a12 : A12 .t a10 a11) (a20 : A20 .t a00 a10)
      (a21 : A21 .t a01 a11)
      → Fib ≔ a00 a01 a02 a10 a11 a12 a20 a21 ↦ (
    Gt a02 a12 a20 a21,
    Gf a00 a01 a02 a10 a11 a12 a20 a21) in
  (Gt,
   pre_univalence_ee A00 A01 A02 A10 A11 A12 A20 A21 Gt Gf
     (isbisim_ee_eqv A00 A01 A02 A10 A11 A12 A20 A21 R G
        (a00 a01 a02 a10 a11 a12 a20 a21 ↦
         Gel_ee_iso (A00 .t) (A01 .t) (A02 .t) (A10 .t) (A11 .t) (A12 .t)
           (A20 .t) (A21 .t) Rt a00 a01 a02 a10 a11 a12 a20 a21) re))
