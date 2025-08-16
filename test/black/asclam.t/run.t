  $ narya asclam.ny -e "axiom C : Type echo ((x : A) ↦ ()) : C → unit"
  x ↦ x
    : (x : A) → A
  
  x ↦ g x (f x)
    : (x : A) → C x
  
  a
    : A
  
  g a (f a)
    : C a
  
  x ↦ ()
    : A → unit
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | axiom C : Type echo ((x : A) ↦ ()) : C → unit
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         C
       does not equal
         A
  
  [1]
