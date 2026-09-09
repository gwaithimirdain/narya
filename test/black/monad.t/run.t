  $ narya -v -monad monad.ny
   ￫ info[I0000]
   ￮ constant ♯ defined
  
   ￫ info[I0000]
   ￮ constant η defined
  
   ￫ info[I0000]
   ￮ constant μ defined
  


Since ♯ is not idempotent, the theory is not locally posetal: there are two distinct cells
♯ ⇒ ♯∘♯ (place the input in the first slot and create the second fresh with the unit, or vice
versa), so neither is picked automatically and this requires an explicit key.

  $ narya -monad monad.ny -e "def ambiguous (A :♯| Type) (x :♯| A) : ♯ (♯ A) := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def ambiguous (A :♯| Type) (x :♯| A) : ♯ (♯ A) := x
     ^ use of ♯ variable behind ♯♯ lock requires a key
  
  [1]


Dually to Comonad (whose counit deletes but has no way to create), a monad's unit creates but
never deletes, so there is no cell ♯ ⇒ id either.

  $ narya -monad monad.ny -e "def no_counit (A :♯| Type) (x :♯| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def no_counit (A :♯| Type) (x :♯| A) : A := x
     ^ use of ♯ variable behind id lock requires a key
  
  [1]


