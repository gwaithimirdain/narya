Testing notation commands

  $ narya -v -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&" y := f x y' -e 'def ff (x y : A) : A := x & y' -e 'axiom a : A' -e 'echo ff a a'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0002]
   ￮ notation «_ & _» defined
  
   ￫ info[I0000]
   ￮ constant ff defined
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
  a & a
    : A
  

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&" y.z := f x y.z'
   ￫ error[E0202]
   ￭ command-line exec string
   1 | notation(0) x "&" y.z := f x y.z
     ^ invalid local variable name: y.z
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "/" := f x x'
   ￫ error[E2207]
   ￮ notation variable 'x' used twice
  
  [1]


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&" y "#" z := f x y'
   ￫ error[E2206]
   ￮ unused notation variable: 'z'
  
  [1]


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "/" := f x y'
   ￫ error[E2208]
   ￮ unbound variable(s) in notation definition: y
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&" y "#" x := f x y'
   ￫ error[E2204]
   ￮ duplicate notation variable: 'x'
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation "#" x "&" y "#" := f x y'

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation x "&" y "#" := f x y'
   ￫ error[E2203]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) "#" x "&" y "#" := f x y'
   ￫ error[E2203]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0.5) x "&" y := f x y' -e 'def ff (x y : A) : A := x & y'


  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0.1) x "&" y := f x y'
   ￫ error[E2200]
   ￭ command-line exec string
   1 | notation(0.1) x "&" y := f x y
     ^ invalid tightness: 0.1
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&x" y := f x y'
   ￫ error[E2201]
   ￮ invalid notation symbol: &x
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&" y := Type x y'
   ￫ error[E2205]
   ￮ invalid notation head: Type
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A' -e 'notation "&" := f'

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&" … "&" y := f x y'
   ￫ error[E0100]
   ￮ unimplemented: internal ellipses in notation
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&" … y := f x y'
   ￫ error[E0100]
   ￮ unimplemented: internal ellipses in notation
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) … := f x y'
   ￫ error[E2202]
   ￮ invalid notation pattern: has no symbols
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) … x "&" y … := f x y'
   ￫ error[E2202]
   ￮ invalid notation pattern: can't be both right and left associative
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A' -e 'notation(0) x := f x'
   ￫ error[E2202]
   ￮ invalid notation pattern: has no symbols
  
  [1]

  $ narya -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) "&" x y := f x y'
   ￫ error[E2202]
   ￮ invalid notation pattern: missing symbol between variables
  
  [1]

  $ narya -v -e 'axiom A:Type' -e 'axiom f:A->A->A' -e 'notation(0) x "&" y := f x y' -e 'notation(0) x "%" y := f x y' -e 'def ff (x y : A) : A := x & y' -e 'def ff2 (x y : A) : A := x % y' -e 'axiom a : A' -e 'echo ff a a' -e 'echo ff2 a a'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0002]
   ￮ notation «_ & _» defined
  
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation «_ % _» defined
  
   ￫ info[I0000]
   ￮ constant ff defined
  
   ￫ info[I0000]
   ￮ constant ff2 defined
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
  a & a
    : A
  
  a & a
    : A
  

This should be an error:

  $ narya -v -e 'axiom A:Type axiom f:A->A->A section nat := notation(0) x "+" y := f x y end axiom a:A echo a + a'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0007]
   ￮ section nat opened
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0008]
   ￮ section nat closed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | axiom A:Type axiom f:A->A->A section nat := notation(0) x "+" y := f x y end axiom a:A echo a + a
     ^ parse error
  

This should work:

  $ narya -v -e 'axiom A:Type axiom f:A->A->A section nat := notation(0) x "+" y := f x y end import nat | only notations axiom a:A echo a + a'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0007]
   ￮ section nat opened
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0008]
   ￮ section nat closed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
  a + a
    : A
  

As should this:

  $ narya -v -e 'axiom A:Type axiom f:A->A->A section nat := notation(0) x "+" y := f x y end import nat | seq (only notations, renaming notations notations.nat) axiom a:A echo a + a'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0007]
   ￮ section nat opened
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0008]
   ￮ section nat closed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
  a + a
    : A
  
