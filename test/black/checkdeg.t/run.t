  $ narya degconstr.ny
  left. (refl a)
    : Sum⁽ᵉ⁾ (Id A) (Id B) (left. a) (left. a)
  
  left. (refl a)
    : Sum⁽ᵉ⁾ (Id A) (Id B) (left. a) (left. a)
  
  nil.
    : List A
  
  cons. (refl a) (cons. (refl a) nil.)
    : List⁽ᵉ⁾ (Id A) (cons. a (cons. a nil.)) (cons. a (cons. a nil.))
  
  cons. a⁽ᵉᵉ⁾ (cons. a⁽ᵉᵉ⁾ nil.)
    : List⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ {cons. a (cons. a nil.)} {cons. a (cons. a nil.)}
        (cons. (refl a) (cons. (refl a) nil.)) {cons. a (cons. a nil.)}
        {cons. a (cons. a nil.)} (cons. (refl a) (cons. (refl a) nil.))
        (cons. (refl a) (cons. (refl a) nil.))
        (cons. (refl a) (cons. (refl a) nil.))
  

  $ narya -e 'import "degconstr" echo refl (cons. a (cons. a nil.)) : List A'
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/degconstr.nyo
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | import "degconstr" echo refl (cons. a (cons. a nil.)) : List A
     ^ degeneracy propagated through constructor
     ^ term synthesized type
         Id A a a
       but is being checked against type
         A
       unequal head terms:
         refl A
       does not equal
         A
  
  [1]

  $ narya degnumeral.ny
  refl 3
    : ℕ⁽ᵉ⁾ 3 3
  
  3⁽ᵉᵉ⁾
    : ℕ⁽ᵉᵉ⁾ {3} {3} (refl 3) {3} {3} (refl 3) (refl 3) (refl 3)
  
  3⁽ᵉᵉ⁾
    : ℕ⁽ᵉᵉ⁾ {3} {3} (refl 3) {3} {3} (refl 3) (refl 3) (refl 3)
  

  $ narya degtuple.ny
  (refl a, refl b)
    : Prod⁽ᵉ⁾ (Id A) (Id B) (a, b) (a, b)
  
  (fst ≔ refl a, snd ≔ refl b)
    : Prod⁽ᵉ⁾ (Id A) (Id B) (a, b) (a, b)
  
  (snd ≔ refl b, fst ≔ refl a)
    : Prod⁽ᵉ⁾ (Id A) (Id B) (a, b) (a, b)
  
  $ narya -v symabs.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a00 assumed
  
   ￫ info[I0001]
   ￮ axiom a01 assumed
  
   ￫ info[I0001]
   ￮ axiom a02 assumed
  
   ￫ info[I0001]
   ￮ axiom a10 assumed
  
   ￫ info[I0001]
   ￮ axiom a11 assumed
  
   ￫ info[I0001]
   ￮ axiom a12 assumed
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0001]
   ￮ axiom a22 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b00 assumed
  
   ￫ info[I0001]
   ￮ axiom b01 assumed
  
   ￫ info[I0001]
   ￮ axiom b02 assumed
  
   ￫ info[I0001]
   ￮ axiom b10 assumed
  
   ￫ info[I0001]
   ￮ axiom b11 assumed
  
   ￫ info[I0001]
   ￮ axiom b12 assumed
  
   ￫ info[I0001]
   ￮ axiom b20 assumed
  
   ￫ info[I0001]
   ￮ axiom b21 assumed
  
   ￫ info[I0001]
   ￮ axiom b22 assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant ab22 defined
  
   ￫ info[I0000]
   ￮ constant sym_ab22 defined
  
   ￫ info[I0000]
   ￮ constant sym_ab22' defined
  
   ￫ info[I0001]
   ￮ axiom f00 assumed
  
   ￫ info[I0001]
   ￮ axiom f01 assumed
  
   ￫ info[I0001]
   ￮ axiom f02 assumed
  
   ￫ info[I0001]
   ￮ axiom f10 assumed
  
   ￫ info[I0001]
   ￮ axiom f11 assumed
  
   ￫ info[I0001]
   ￮ axiom f12 assumed
  
   ￫ info[I0001]
   ￮ axiom f20 assumed
  
   ￫ info[I0001]
   ￮ axiom f21 assumed
  
   ￫ info[I0001]
   ￮ axiom f22 assumed
  
   ￫ info[I0000]
   ￮ constant etaf22 defined
  
   ￫ info[I0000]
   ￮ constant eta_symf22 defined
  
   ￫ info[I0000]
   ￮ constant eta_symf22' defined
  

