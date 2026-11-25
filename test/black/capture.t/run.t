Constants are displayed by name, so they must not be captured by local variables with the same names.

  $ narya capture.ny
  (A′ : A) → A
    : Type
  
  (A′ : A) (A′′ : A) → A
    : Type
  
  (A : A) → B
    : Type
  
  (A′ : A) → A
    : Type
  
  {A′ : A} {x₁ : A} (x₂ : Id A A′ x₁) →⁽ᵉ⁾ Id C x₂ (f A′) (f x₁)
    : Type
  

  $ narya -v holes.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant K defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     A : Type
     y : _root_.A
     ----------------------------------------------------------------------
     _root_.A
  
   ￫ info[I0000]
   ￮ constant L defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     z : _root_.A
     A : Type
     ----------------------------------------------------------------------
     Type
  
   ￫ error[E3002]
   ￮ file holes.ny contains open holes
  
  [1]

The same goes for terms in error messages, which are displayed in the context of the variables in scope.

  $ narya -e "axiom A : Type" -e "def bad (A : Type) (y : _root_.A) : A ≔ y"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def bad (A : Type) (y : _root_.A) : A ≔ y
     ^ term synthesized type
         _root_.A
       but is being checked against type
         A
       unequal head terms:
         _root_.A
       does not equal
         A
  
  [1]
