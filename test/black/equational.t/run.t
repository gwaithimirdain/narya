  $ narya -v equational.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom x assumed
  
   ￫ info[I0001]
   ￮ axiom y assumed
  
   ￫ info[I0001]
   ￮ axiom z assumed
  
   ￫ info[I0001]
   ￮ axiom w assumed
  
   ￫ info[I0001]
   ￮ axiom p assumed
  
   ￫ info[I0001]
   ￮ axiom q assumed
  
   ￫ info[I0001]
   ￮ axiom r assumed
  
   ￫ info[I0000]
   ￮ constant xx defined
  
   ￫ info[I0000]
   ￮ constant xy defined
  
   ￫ info[I0000]
   ￮ constant xydef defined
  
   ￫ info[I0000]
   ￮ constant xyz defined
  
   ￫ info[I0000]
   ￮ constant xyzdef defined
  
   ￫ info[I0000]
   ￮ constant xyzw defined
  
   ￫ info[I0000]
   ￮ constant xyzwdef defined
  
   ￫ info[I0001]
   ￮ axiom s assumed
  
   ￫ info[I0000]
   ￮ constant xz' defined
  
   ￫ info[I0000]
   ￮ constant xz'def defined
  
   ￫ info[I0000]
   ￮ constant xz'' defined
  
   ￫ info[I0000]
   ￮ constant xz''def defined
  
   ￫ info[I0000]
   ￮ constant xz''' defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant plus defined
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0000]
   ￮ constant 2plus3 defined
  
   ￫ info[I0000]
   ￮ constant ℕ.plus_assoc defined
  

A step marked with ← is checked only in the reversed orientation.

  $ narya equational.ny -e "def xy' : Id A x y ≔ calc x = y by ← p ∎"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def xy' : Id A x y ≔ calc x = y by ← p ∎
     ^ term synthesized type
         Id A x y
       but is being checked against type
         Id A y x
       unequal head constants:
         x
       does not equal
         y
  
  [1]

The marker applies to a proof term, including applications and nested calc
blocks. Arrow identifiers and user notation still work inside terms.

  $ narya -source-only -no-write-compiled -no-reformat markers.ny

Both spellings select the reversed type, with no fallback to the forward type.

  $ narya -source-only -no-write-compiled -no-reformat equational.ny -e "def xy_ascii : Id A x y ≔ calc x = y by <- p ∎"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def xy_ascii : Id A x y ≔ calc x = y by <- p ∎
     ^ term synthesized type
         Id A x y
       but is being checked against type
         Id A y x
       unequal head constants:
         x
       does not equal
         y
  
  [1]

The formatter preserves comments and writes a space after the marker.
Both output modes must parse and remain unchanged after a second pass.

  $ cat format.ny > formatted.ny
  $ narya -source-only -no-write-compiled formatted.ny
  $ cat formatted.ny
  import "equational"
  
  def unicode : Id A y z ≔ calc
    y
    = z
        by {` before `} ← {` after `} s ∎
  
  def ascii : Id A y z ≔ calc
    y
    = z
        by ← s ∎
  $ cp formatted.ny unicode.ny
  $ narya -source-only -no-write-compiled formatted.ny
  $ diff unicode.ny formatted.ny
  $ narya -source-only -no-write-compiled -ascii formatted.ny
  $ cat formatted.ny
  import "equational"
  
  def unicode : Id A y z := calc
    y
    = z
        by {` before `} <- {` after `} s ∎
  
  def ascii : Id A y z := calc
    y
    = z
        by <- s ∎
  $ cp formatted.ny ascii.ny
  $ narya -source-only -no-write-compiled -ascii formatted.ny
  $ diff ascii.ny formatted.ny
  $ narya -source-only -no-write-compiled formatted.ny
  $ diff unicode.ny formatted.ny
