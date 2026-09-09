  $ narya -v -ambiflection ambiflection.ny
   ￫ info[I0000]
   ￮ constant □△ defined
  
   ￫ info[I0000]
   ￮ constant eta defined
  
   ￫ info[I0000]
   ￮ constant eta_inv defined
  
   ￫ info[I0000]
   ￮ constant eta_inv2 defined
  
   ￫ info[I0000]
   ￮ constant counit defined
  
   ￫ info[I0000]
   ￮ constant tribox defined
  
   ￫ info[I0000]
   ￮ constant wu defined
  
   ￫ info[I0000]
   ￮ constant roundtrip_good defined
  
   ￫ info[I0000]
   ￮ constant roundtrip_good_ok defined
  
   ￫ info[I0000]
   ￮ constant Neg defined
  
   ￫ info[I0000]
   ￮ constant mk defined
  
   ￫ info[I0000]
   ￮ constant unmk defined
  
   ￫ info[I0000]
   ￮ constant unmk_mk defined
  
   ￫ info[I0000]
   ￮ constant □ defined
  
   ￫ info[I0000]
   ￮ constant box defined
  
   ￫ info[I0000]
   ￮ constant unbox defined
  
   ￫ info[I0000]
   ￮ constant unbox_box defined
  
   ￫ info[I0000]
   ￮ constant △ defined
  
   ￫ info[I0000]
   ￮ constant tri defined
  
   ￫ info[I0000]
   ￮ constant untri defined
  
   ￫ info[I0000]
   ￮ constant untri_tri defined
  
   ￫ info[I0000]
   ￮ constant zero defined
  
   ￫ info[I0000]
   ￮ constant zero△□ defined
  

Composing the unit and then the counit, id ⇒ △□ ⇒ id, is "zero", not the identity: applying
counit to a genuinely plain value (which needs the unit inserted first) does not typecheck.

  $ narya -ambiflection ambiflection.ny -e "def roundtrip_bad (A : Type) (x : A) : A ≔ counit A x"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def roundtrip_bad (A : Type) (x : A) : A ≔ counit A x
     ^ term synthesized type
         A
       but is being checked against type
         A
       unequal head terms:
         A
       does not equal
         A
  
  [1]

We get the same error here:

  $ narya -ambiflection -e "def zero (A : Type) (a : A) : A ≔ a #ø"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def zero (A : Type) (a : A) : A ≔ a #ø
     ^ term synthesized type
         A
       but is being checked against type
         A
       unequal head terms:
         A
       does not equal
         A
  
  [1]

The nonparametric ambiflection mode theory currently requires -parametric.

  $ narya -discrete-ambiflection discrete_ambiflection.ny
  -discrete-ambiflection requires -parametric
  [1]

And -external is not allowed with it.

  $ narya -parametric -direction p,rel,Br -arity 1 -discrete-ambiflection -external discrete_ambiflection.ny
  -external requires a compatible mode theory
  [1]

Since there is a 2-cell (the □ ⊣ △ unit) from the non-discrete identity modality to the discrete
modality △□, the arity of parametricity must be 1.

  $ narya -parametric -direction p,rel,Br -discrete-ambiflection discrete_ambiflection.ny
  -discrete-ambiflection requires -arity 1
  [1]

Under arity 1, using a △□-locked argument filters out the parametric dimension, exactly as for
-discrete-ambiflector's ♮ and -discrete-tconn's △◇.

  $ narya -v -parametric -direction p,rel,Br -arity 1 -discrete-ambiflection discrete_ambiflection.ny
   ￫ info[I0001]
   ￮ axiom X assumed
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom x₀ assumed
  
   ￫ info[I0001]
   ￮ axiom x₁ assumed
  
  rel (x ↦ f x (a x)) x₁
    : Br B (f x₀ (a x₀))
  
  rel f x₁ (a x₀)
    : Br B (f x₀ (a x₀))
  
