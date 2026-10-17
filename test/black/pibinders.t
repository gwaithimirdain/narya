A group of variables in a pi-type sharing a domain, such as "(x y : A)", binds all of them at once.  Their domain is processed and typechecked only once, in the scope outside all of them.  In particular, it can't refer to the earlier variables of the same group.

  $ cat >pi.ny <<EOF
  > axiom A : Type
  > axiom B : Type
  > axiom a : A
  > axiom b : B
  > EOF

  $ narya pi.ny -e 'echo (A y : A) → Type  echo (x y : A) (z : B) → A → B'
  (A : A) (y : A) → Type
    : Type
  
  (x : A) (y : A) (z : B) → A → B
    : Type
  

A hole in the shared domain is created only once, and is shared by all the variables.

  $ narya -v pi.ny -fake-interact 'def t : (x y : ?) → Type ≔ ?  solve 0 ≔ A  echo t'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0000]
   ￮ constant t defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     (x : ?0{…}) (y : ?0{…}) → Type
  
   ￫ info[I0005]
   ￮ hole solved
  
  t
    : (x : A) (y : A) → Type
  

The same is true for a modal domain.

  $ narya -v -spatial pi.ny -fake-interact 'def t : (x y :♭| ?) → Type ≔ ?  solve 0 ≔ A  echo t'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0000]
   ￮ constant t defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     (x :♭| ?0{…}) (y :♭| ?0{…}) → Type
  
   ￫ info[I0005]
   ￮ hole solved
  
  t
    : (x :♭| A) (y :♭| A) → Type
  

A datatype constructor whose type is given as a pi-type takes the domains of that pi-type as its arguments, including groups of variables sharing a domain.

  $ narya pi.ny -e 'def D : Type ≔ data [ c. : (x y : A) → D | d. : A → (B → D) | e. : ((x : A) → D) ]  echo (c. a a : D)  echo (d. a b : D)  echo (e. a : D)'
  c. a a
    : D
  
  d. a b
    : D
  
  e. a
    : D
  
