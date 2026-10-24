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
  

In a mutual block, the variables bound to the other local definitions are not displayed as bindings, but are referred to by name.

  $ cat >eo.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def bool : Type ≔ data [ true. | false. ]
  > def eo (m : ℕ) : bool ≔
  >   let rec even : ℕ → bool ≔ [ zero. ↦ true. | suc. n ↦ odd n ]
  >   and odd : ℕ → bool ≔ [ zero. ↦ false. | suc. n ↦ even n ] in
  >   even m
  > def eo2 : ℕ → bool ≔
  >   let rec even : ℕ → bool ≔ [ zero. ↦ true. | suc. n ↦ odd n ]
  >   and odd : ℕ → bool ≔ [ zero. ↦ false. | suc. n ↦ even n ] in
  >   odd
  > axiom k : ℕ
  > EOF

  $ narya eo.ny -e 'echo eo (suc. k)' -e 'echo eo2'
  (let only … in _letrec.F2.1.odd) k
    : bool
  
  _letrec.F2.3.odd
    : ℕ → bool
  
  $ narya eo.ny -e 'display let ≔ environments' -e 'echo eo (suc. k)' -e 'echo eo2'
  (let only m : ℕ ≔ suc. k in _letrec.F2.1.odd) k
    : bool
  
  _letrec.F2.3.odd
    : ℕ → bool
  
  $ narya eo.ny -e 'display let ≔ definitions' -e 'echo eo (suc. k)' -e 'echo eo2'
  (let only m : ℕ ≔ suc. k in
   (𝑥 ↦ match 𝑥 [ suc. n ↦ _letrec.F2.0.even n | zero. ↦ false. ] : ℕ → bool))
    k
    : bool
  
  𝑥 ↦ match 𝑥 [ suc. n ↦ _letrec.F2.2.even n | zero. ↦ false. ]
    : ℕ → bool
  

Variables bound to local definitions from other blocks, such as enclosing ones, are displayed as usual.

  $ cat >nested.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def bool : Type ≔ data [ true. | false. ]
  > def h (m : ℕ) : bool ≔
  >   let rec f : ℕ → bool ≔ [ zero. ↦ true. | suc. n ↦ f n ] in
  >   let rec g : ℕ → bool ≔ [ zero. ↦ f m | suc. n ↦ g n ]
  >   and g2 : ℕ → bool ≔ [ zero. ↦ g m | suc. n ↦ g2 n ] in
  >   g2 m
  > axiom k : ℕ
  > EOF

  $ narya nested.ny -e 'display let ≔ environments' -e 'echo h k'
  (let only m : ℕ ≔ k
   and f : ℕ → bool ≔ let only m : ℕ ≔ k in _letrec.F2.0.f in
   _letrec.F2.2.g2) k
    : bool
  
  $ narya nested.ny -e 'display let ≔ definitions' -e 'echo h k'
  (let only m : ℕ ≔ k
   and f : ℕ → bool ≔
     let only m : ℕ ≔ k in
     (𝑥 ↦ match 𝑥 [ suc. n ↦ _letrec.F2.0.f n | zero. ↦ true. ] : ℕ → bool)
   in
   (𝑥 ↦ match 𝑥 [ suc. n ↦ _letrec.F2.2.g2 n | zero. ↦ _letrec.F2.1.g m ]
    : ℕ → bool)) k
    : bool
  

An ascribed definition displayed as the value of a let-only clause doesn't leave its opening parenthesis alone on a line.

  $ narya -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]  axiom z : ℕ  axiom f : ℕ → ℕ → ℕ' -e 'display let ≔ definitions' -e 'def t (x : ℕ) : ℕ → ℕ ≔ let a : ℕ → ℕ ≔ let c ≔ f x x in let d : ℕ → ℕ ≔ (let e ≔ f (f x x) (f x c) in [ zero. ↦ f (f e e) (f e e) | suc. _ ↦ f (f z z) (f z z) ]) in [ zero. ↦ f (f (d z) (d z)) (d z) | suc. _ ↦ f (f z z) (f z z) ] in let b : ℕ → ℕ ≔ [ zero. ↦ a z | suc. _ ↦ z ] in b' -e 'echo t z'
  let only x : ℕ ≔ z
  and a : ℕ → ℕ ≔
    let only x : ℕ ≔ z in
    (let c ≔ f x x in
     let d ≔
       let e ≔ f (f x x) (f x c) in
       𝑥 ↦ match 𝑥 [ suc. 𝑦 ↦ f (f z z) (f z z) | zero. ↦ f (f e e) (f e e) ]
     in
     𝑥 ↦
     match 𝑥 [ suc. 𝑦 ↦ f (f z z) (f z z) | zero. ↦ f (f (d z) (d z)) (d z) ]
     : ℕ → ℕ) in
  (𝑥 ↦ match 𝑥 [ suc. 𝑦 ↦ z | zero. ↦ a z ] : ℕ → ℕ)
    : ℕ → ℕ
  
