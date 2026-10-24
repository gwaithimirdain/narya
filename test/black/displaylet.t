The "display let" option controls how local definitions (let-bound case trees) and holes are displayed when they appear outside their own context, i.e. with a substitution applied.

  $ cat >dl.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def sq (f : ℕ → ℕ) : ℕ → ℕ ≔ x ↦ f (f x)
  > def sqdec (x : ℕ) : ℕ ≔
  >   let dec : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ n ] in
  >   sq dec x
  > axiom z : ℕ
  > EOF

By default, they are displayed by name, with the substitution elided.

  $ narya dl.ny -e 'echo sqdec z'
  (let only … in _let.F2.0.dec) ((let only … in _let.F2.0.dec) z)
    : ℕ
  
  $ narya dl.ny -e 'display let ≔ environments' -e 'echo sqdec z'
  (let only x : ℕ ≔ z in _let.F2.0.dec)
    ((let only x : ℕ ≔ z in _let.F2.0.dec) z)
    : ℕ
  
  $ narya dl.ny -e 'display let ≔ definitions' -e 'echo sqdec z'
  (let only x : ℕ ≔ z in (𝑥 ↦ match 𝑥 [ suc. n ↦ n | zero. ↦ 0 ] : ℕ → ℕ))
    ((let only x : ℕ ≔ z in (𝑥 ↦ match 𝑥 [ suc. n ↦ n | zero. ↦ 0 ] : ℕ → ℕ))
       z)
    : ℕ
  
  $ narya dl.ny -ascii -e 'echo sqdec z'
  (let only ... in _let.F2.0.dec) ((let only ... in _let.F2.0.dec) z)
    : ℕ
  

The option can also be cycled.

  $ narya -v -e 'display let ≔ cycle' -e 'display let ≔ cycle' -e 'display let ≔ cycle'
   ￫ info[I0101]
   ￮ display set let to environments
  
   ￫ info[I0101]
   ￮ display set let to definitions
  
   ￫ info[I0101]
   ￮ display set let to names
  

Holes have no definitions, so they are displayed by name with "definitions" too.

  $ narya dl.ny -fake-interact 'def f (x : ℕ) : ℕ ≔ sq (y ↦ y) ?  echo f z  display let ≔ environments  echo f z  display let ≔ definitions  echo f z'
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     x : ℕ
     ----------------------------------------------------------------------
     ℕ
  
  let only … in ?0
    : ℕ
  
   ￫ info[I0101]
   ￮ display set let to environments
  
  let only x : ℕ ≔ z in ?0
    : ℕ
  
   ￫ info[I0101]
   ￮ display set let to definitions
  
  let only x : ℕ ≔ z in ?0
    : ℕ
  

A recursive local definition refers to itself by name.

  $ narya -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]  def bool : Type ≔ data [ true. | false. ]' -e 'display let ≔ definitions' -e 'def ev (m : ℕ) : bool ≔ let rec even : ℕ → bool ≔ [ zero. ↦ true. | suc. n ↦ even n ] in even m' -e 'axiom k : ℕ' -e 'echo ev (suc. k)'
  (let only m : ℕ ≔ suc. k in
   (𝑥 ↦ match 𝑥 [ suc. n ↦ _letrec.F4.0.even n | zero. ↦ true. ] : ℕ → bool))
    k
    : bool
  
