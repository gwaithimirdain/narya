{` -*- narya-prog-args: ("-proofgeneral" "-direction" "p,rel,Br") -*- `}

import "isfibrant"
import "fibrant_types"
import "bookhott"
import "hott_bookhott"
import "homotopy"

option function boundaries ≔ implicit
option type boundaries ≔ implicit

axiom A00 : Fib
axiom A01 : Fib
axiom A02 : Br Fib A00 A01
axiom A10 : Fib
axiom A11 : Fib
axiom A12 : Br Fib A10 A11
axiom A20 : Br Fib A00 A10
axiom A21 : Br Fib A01 A11
axiom A22 : Fib⁽ᵖᵖ⁾ A02 A12 A20 A21

axiom B00 : A00 .t → Fib
axiom B01 : A01 .t → Fib
axiom B02 : Br ((X ↦ X → Fib) : Type → Type) (A02 .t) B00 B01
axiom B10 : A10 .t → Fib
axiom B11 : A11 .t → Fib
axiom B12 : Br ((X ↦ X → Fib) : Type → Type) (A12 .t) B10 B11
axiom B20 : Br ((X ↦ X → Fib) : Type → Type) (A20 .t) B00 B10
axiom B21 : Br ((X ↦ X → Fib) : Type → Type) (A21 .t) B01 B11
axiom B22 : ((X ↦ X → Fib) : Type → Type)⁽ᵖᵖ⁾ (A22 .t) B02 B12 B20 B21

axiom f00 : (x00 : A00 .t) → B00 x00 .t
axiom f01 : (x01 : A01 .t) → B01 x01 .t
axiom f02
  : Br ((X Y ↦ Π𝕗 X Y) : ((X : Fib) (Y : X .t → Fib) → Fib)) A02 B02
  .t f00 f01

axiom a10 : A10 .t
axiom a11 : A11 .t
axiom a12 : A12 .t a10 a11

{` 1-uniform transport acting on 1-dimensional functions `}
echo ((X Y ↦ Π𝕗 X Y) : ((X : Fib) (Y : X .t → Fib) → Fib))⁽ᵖᵖ⁾ A22 B22
  .f
  .trr.1 f02 a12
{` B22 (A22 .f .liftl.1 a12) .f .trr.1 (f02 (A22 .f .trl.1 a12))

  : B12 a12
  .t (B20 (A20 .f .liftl.1 a10) .f .trr.1 (f00 (A20 .f .trl.1 a10)))
    (B21 (A21 .f .liftl.1 a11) .f .trr.1 (f01 (A21 .f .trl.1 a11)))
 `}

axiom f10 : (x10 : A10 .t) → B10 x10 .t
axiom f11 : (x11 : A11 .t) → B11 x11 .t
axiom f12
  : Br ((X Y ↦ Π𝕗 X Y) : ((X : Fib) (Y : X .t → Fib) → Fib)) A12 B12
  .t f10 f11
axiom f20
  : Br ((X Y ↦ Π𝕗 X Y) : ((X : Fib) (Y : X .t → Fib) → Fib)) A20 B20
  .t f00 f10
axiom f21
  : Br ((X Y ↦ Π𝕗 X Y) : ((X : Fib) (Y : X .t → Fib) → Fib)) A21 B21
  .t f01 f11

axiom a01 : A01 .t
axiom a21 : A21 .t a01 a11

{` 1-box-filling acting on 1-dimensional functions `}
echo ((X Y ↦ Π𝕗 X Y) : ((X : Fib) (Y : X .t → Fib) → Fib))⁽ᵖᵖ⁾ A22 B22
  .f
  .id.1 f02 f12
  .trr.1 f20 a21
{` B22 (A22 .f .id.1 (A02 .f .liftl.1 a01) (A12 .f .liftl.1 a11) .liftl.1 a21)
  .f
  .id.1 (f02 (A02 .f .liftl.1 a01)) (f12 (A12 .f .liftl.1 a11))
  .trr.1
    (f20
       (A22 .f .id.1 (A02 .f .liftl.1 a01) (A12 .f .liftl.1 a11) .trl.1 a21))

  : B21 a21 .t (f01 a01) (f11 a11)
 `}

{` Double-check that the computed result indeed has the correct type. `}
{` TODO: Oops formatting!  The A22 should be on the previous line or indented less. `}
echo B22
         (A22
          .f
          .id.1 (A02 .f .liftl.1 a01) (A12 .f .liftl.1 a11)
          .liftl.1 a21)
  .f
  .id.1 (f02 (A02 .f .liftl.1 a01)) (f12 (A12 .f .liftl.1 a11))
  .trr.1
    (f20
       (A22 .f .id.1 (A02 .f .liftl.1 a01) (A12 .f .liftl.1 a11) .trl.1 a21))

{` Note that the above uses box-filling in A where the tube consists of lifts.  This operation has the same type as 1-uniform transport, so we could just as well use that.  It doesn't give the *same* result, but it would be another valid, and simpler-looking definition.  The coinductive definition of 𝕗Π can't give this simpler version; the builtin fibrancy of Π-types could, but that would require defining it at all dimensions directly rather than coinductively, which is simpler. `}

{` That is, these have the same type: `}
echo (A22 .f .id.1 (A02 .f .liftl.1 a01) (A12 .f .liftl.1 a11) .trl.1 a21)
echo (A22 .f .trl.2 a21)

{` And the types of these differ only by switching out the previous two. `}
echo (A22 .f .id.1 (A02 .f .liftl.1 a01) (A12 .f .liftl.1 a11) .liftl.1 a21)
echo (sym (A22 .f .liftl.2 a21))

{` So we could use this instead. `}
echo B22 (sym (A22 .f .liftl.2 a21))
  .f
  .id.1 (f02 (A02 .f .liftl.1 a01)) (f12 (A12 .f .liftl.1 a11))
  .trr.1 (f20 ((A22 .f .trl.2 a21)))
{` B22 (sym (sym A22 .f .liftl.1 a21))
  .f
  .id.1 (f02 (A02 .f .liftl.1 a01)) (f12 (A12 .f .liftl.1 a11))
  .trr.1 (f20 (sym A22 .f .trl.1 a21))

  : B21 a21 .t (f01 a01) (f11 a11)
 `}

{` However, we *can't* use 1-uniform transport in B, since for the result to have the correct type, the tube needs to consist of the actions of the tube functions f02 and f12, not lifts of the actions of f00 and f10. `}

echo sym B22 (A22 .f .liftl.2 a21) .f .trr.1 (f20 (A22 .f .trl.2 a21))
{` sym B22 (sym A22 .f .liftl.1 a21) .f .trr.1 (f20 (sym A22 .f .trl.1 a21))

  : B21 a21
  .t (B02 (A02 .f .liftl.1 a01) .f .trr.1 (f00 (A02 .f .trl.1 a01)))
    (B12 (A12 .f .liftl.1 a11) .f .trr.1 (f10 (A12 .f .trl.1 a11)))
 `}
