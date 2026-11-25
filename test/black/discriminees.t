In a match with several discriminees, the later ones are processed only once, outside the whole match.  A discriminee that is a variable is matched against as that variable in every branch, so the match can still refine it.

  $ cat >disc.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def F (n : ℕ) : Type ≔ match n [ zero. ↦ ℕ | suc. _ ↦ ℕ ]
  > def double (m : ℕ) : ℕ ≔ match m [ zero. ↦ zero. | suc. k ↦ suc. (suc. (double k)) ]
  > EOF

  $ narya disc.ny -e 'def pred (n : ℕ) (x : F n) : ℕ ≔ match n, x [ zero., zero. ↦ zero. | zero., suc. y ↦ y | suc. _, zero. ↦ zero. | suc. _, suc. y ↦ y ]  echo pred 3 5'
  4
    : ℕ
  

Any other discriminee is let-bound outside the whole match, so it is typechecked in the context outside the match, even if it would make sense in the branches of the earlier matches.

  $ narya disc.ny -e 'def pred (n : ℕ) (x : F n) : ℕ ≔ match n, double x [ zero., zero. ↦ zero. | zero., suc. y ↦ y | suc. _, zero. ↦ zero. | suc. _, suc. y ↦ y ]'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def pred (n : ℕ) (x : F n) : ℕ ≔ match n, double x [ zero., zero. ↦ zero. | zero., suc. y ↦ y | suc. _, zero. ↦ zero. | suc. _, suc. y ↦ y ]
     ^ term synthesized type
         F n
       but is being checked against type
         ℕ
       unequal head constants:
         F
       does not equal
         ℕ
  
  [1]

The let-bound variable appears in the contexts of holes, and matching against it is non-dependent, without a hint.

  $ narya -v disc.ny -fake-interact 'def f (n m : ℕ) : ℕ ≔ match n, double m [ zero., zero. ↦ zero. | zero., suc. y ↦ ? | suc. _, y ↦ y ]  about f'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant F defined
  
   ￫ info[I0000]
   ￮ constant double defined
  
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     n ≔ 0 : ℕ
     m : ℕ
     𝑥 ≔ double m : ℕ (not in scope)
     y : ℕ
     ----------------------------------------------------------------------
     ℕ
  
  n m ↦
  let 𝑥 ≔ double m in
  match n [ suc. 𝑦 ↦ 𝑥 | zero. ↦ match 𝑥 [ suc. y ↦ ?0 | zero. ↦ 0 ] ]
    : (n : ℕ) (m : ℕ) → ℕ
  
