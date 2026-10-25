A local definition whose value is a case tree is named after the constant in whose definition it appears and the variable it is bound to.  Repeated names in the same definition are distinguished by primes, avoiding the names of other local definitions.

  $ cat >names.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def f (k : ℕ) : ℕ ≔
  >   let x : ℕ → ℕ ≔ y ↦ match y [ zero. ↦ zero. | suc. n ↦ n ] in
  >   let x′ : ℕ → ℕ ≔ y ↦ match y [ zero. ↦ k | suc. n ↦ n ] in
  >   let x : ℕ → ℕ ≔ y ↦ match y [ zero. ↦ suc. k | suc. n ↦ n ] in
  >   ?
  > EOF

  $ narya -v names.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     k : ℕ
     x″ ≔ f._x : ℕ → ℕ (not in scope)
     x′ ≔ f._x′ : ℕ → ℕ
     x ≔ f._x″ : ℕ → ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ error[E3002]
   ￮ file names.ny contains open holes
  
  [1]

A local definition that is checked more than once, as here where the outer one is first tried as an ordinary term, gets the same name each time.

  $ cat >retry.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def f (k : ℕ) : ℕ ≔
  >   let a : ℕ → ℕ ≔ (
  >     let b : ℕ → ℕ ≔ y ↦ match y [ zero. ↦ k | suc. n ↦ n ] in
  >     y ↦ match y [ zero. ↦ ? | suc. n ↦ n ]) in
  >   a k
  > EOF

  $ narya -v retry.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     k : ℕ
     b ≔ f._b : ℕ → ℕ
     y ≔ 0 : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ error[E3002]
   ￮ file retry.ny contains open holes
  
  [1]

Local definitions in the types of definitions and axioms are named after them too.  Outside of any definition, the constant is replaced by the origin and autonumber.

  $ cat >types.ny <<EOF
  > axiom u : let T : Type ≔ data [ a. ] in T
  > def v : let S : Type ≔ data [ b. ] in S ≔ b.
  > synth u
  > synth v
  > echo let x : Type ≔ data [ c. ] in x
  > EOF

  $ narya types.ny
  u
    : u._T
  
  v
    : v._S
  
  F2.2._x
    : Type
  

Local definitions in a term that solves a hole, or that is echoed in the context of a hole, are named after the definition containing the hole.

  $ cat >solve.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def g (k : ℕ) : ℕ ≔
  >   let x : ℕ → ℕ ≔ y ↦ match y [ zero. ↦ zero. | suc. n ↦ n ] in
  >   ?
  > solve 0 ≔ let x : ℕ → ℕ ≔ y ↦ match y [ zero. ↦ k | suc. n ↦ n ] in ?
  > echo in 1 let z : Type ≔ data [ c. ] in z
  > EOF

  $ narya -v -fake-interact solve.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant g defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     k : ℕ
     x ≔ g._x : ℕ → ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0005]
   ￮ hole solved, containing 1 new hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     k : ℕ
     x′ ≔ g._x : ℕ → ℕ (not in scope)
     x ≔ g._x′ : ℕ → ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     k : ℕ
     x′ ≔ g._x : ℕ → ℕ (not in scope)
     x ≔ g._x′ : ℕ → ℕ
     ----------------------------------------------------------------------
     ℕ
  
  g._z
    : Type
  
