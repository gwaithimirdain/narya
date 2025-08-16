axiom A : Type
axiom a : A
axiom f : A → A

axiom x : A
axiom y : A
axiom xy : Id A x y

{`Records and datatypes`}
def Σ : (A : Type) → (A → Type) → Type ≔ A B ↦ sig ( fst : A, snd : B fst )
def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
def Nat : Type ≔ ℕ

axiom B : A → Type
axiom s : Σ A B

{`To test degeneracies on records we have to set up a bunch of stuff, since the simplest case this happens is with Id Gel and squares in the universe.`}
def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ (
  ungel : R a b )

axiom A0 : Type
axiom B0 : Type
axiom R0 : A0 → B0 → Type
axiom A1 : Type
axiom B1 : Type
axiom R1 : A1 → B1 → Type
axiom A2 : Id Type A0 A1
axiom B2 : Id Type B0 B1
axiom R2 : refl ((X ↦ Y ↦ (X → Y → Type)) : Type → Type → Type) A2 B2 R0 R1
axiom a0 : A0
axiom a1 : A1
axiom a2 : A2 a0 a1
axiom b0 : B0
axiom b1 : B1
axiom b2 : B2 b0 b1
axiom r0 : R0 a0 b0
axiom r1 : R1 a1 b1
axiom r2 : R2 a2 b2 r0 r1


def r2ty ≔ refl Gel A2 B2 R2 a2 b2 (ungel ≔ r0) (ungel ≔ r1)

def symr2ty
  ≔ sym (refl Gel A2 B2 R2) {a0} {b0} (ungel ≔ r0) {a1} {b1} (ungel ≔ r1) a2
      b2

axiom gg : r2ty

axiom gg' : symr2ty

{`Cube variables`}
axiom af : A → Id (A → A) f f

{`Stream`}
def Stream : (A : Type) → Type ≔ A ↦ codata [
| _ .head : A
| _ .tail : Stream A ]
def zeros : Stream ℕ ≔ [ .head ↦ 0 | .tail ↦ zeros ]
axiom idz : Id (Stream ℕ) zeros zeros
