axiom A : Type
axiom x : A
axiom y : A
axiom z : A
axiom w : A

axiom p : Id A x y
axiom q : Id A y z
axiom r : Id A z w

def xx : Id A x x ≔ calc
  x ∎

def xy : Id A x y ≔ calc
  x
  = y
      by p ∎

def xydef : Id (Id A x y) xy (A⁽ᵉᵉ⁾ (refl x) p .trr (refl x)) ≔ refl xy

def xyz : Id A x z ≔ calc
  x
  = y
      by p
  = y
  = z
      by q ∎

def xyzdef
  : Id (Id A x z) xyz
      (A⁽ᵉᵉ⁾ (refl x) q .trr (A⁽ᵉᵉ⁾ (refl x) p .trr (refl x)))
  ≔ refl xyz

def xyzw : Id A x w ≔ calc
  x
  = x
  = y
      by p
  = z
      by q
  = w
      by r
  = w ∎

def xyzwdef
  : Id (Id A x w) xyzw
      (A⁽ᵉᵉ⁾ (refl x) r
       .trr (A⁽ᵉᵉ⁾ (refl x) q .trr (A⁽ᵉᵉ⁾ (refl x) p .trr (refl x))))
  ≔ refl xyzw

axiom s : Id A z y

def xz' : Id A x z ≔ calc
  x
  = y
      by p
  = z
      by s ∎

def xz'def
  : Id (Id A x z) xz'
      (A⁽ᵉᵉ⁾ (refl x) s .trl (A⁽ᵉᵉ⁾ (refl x) p .trr (refl x)))
  ≔ refl xz'

def ℕ : Type ≔ data [ zero. : ℕ | suc. : ℕ → ℕ ]
def plus (m n : ℕ) : ℕ ≔ match m [ zero. ↦ n | suc. m' ↦ suc. (plus m' n) ]

notation(0) … m "+" n ≔ plus m n

def 2plus3 : Id ℕ (2 + 3) 5 ≔ calc
  2 + 3
  = suc. (1 + 3)
  = suc. (suc. (0 + 3))
  = suc. (suc. 3)
  = 5 ∎

def ℕ.plus_assoc (m n p : ℕ) : Id ℕ ((m + n) + p) (m + (n + p)) ≔ match m [
| zero. ↦ calc
    (zero. + n) + p
    = n + p
    = zero. + (n + p) ∎
| suc. m ↦ calc
    (suc. m + n) + p
    = suc. (m + n) + p
    = suc. ((m + n) + p)
    = suc. (m + (n + p))
        by suc. (ℕ.plus_assoc m n p)
    = suc. m + (n + p) ∎]
