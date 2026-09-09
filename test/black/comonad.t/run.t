  $ narya -v -comonad comonad.ny
   ￫ info[I0000]
   ￮ constant ♭ defined
  
   ￫ info[I0000]
   ￮ constant counit defined
  
   ￫ info[I0000]
   ￮ constant ε defined
  
   ￫ info[I0000]
   ￮ constant δ defined
  
   ￫ info[I0000]
   ￮ constant counit_law defined
  


Since ♭ is not idempotent (there is no isomorphism ♭∘♭ ⇒ ♭), the theory is not locally posetal:
there are two distinct cells ♭∘♭ ⇒ ♭ (counit the first ♭ and keep the second, or vice versa), so
neither is picked automatically and this requires an explicit key.

  $ narya -comonad comonad.ny -e "def ambiguous (A :♭♭| Type) (x :♭♭| A) : ♭ A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def ambiguous (A :♭♭| Type) (x :♭♭| A) : ♭ A := x
     ^ use of ♭♭ variable behind ♭ lock requires a key
  
  [1]


