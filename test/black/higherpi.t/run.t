  $ narya -v higherpi.ny -e "echo Id ((x : A) → B x) f g" -e "echo ((x : A) → B x)⁽ᵉᵉ⁾ f02 f12 f20 f21" -e "echo Id ((x : A) → B x)"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
   ￫ info[I0000]
   ￮ constant idok defined
  
   ￫ info[I0001]
   ￮ axiom f00 assumed
  
   ￫ info[I0001]
   ￮ axiom f01 assumed
  
   ￫ info[I0001]
   ￮ axiom f10 assumed
  
   ￫ info[I0001]
   ￮ axiom f11 assumed
  
   ￫ info[I0001]
   ￮ axiom f02 assumed
  
   ￫ info[I0001]
   ￮ axiom f12 assumed
  
   ￫ info[I0001]
   ￮ axiom f20 assumed
  
   ￫ info[I0001]
   ￮ axiom f21 assumed
  
   ￫ info[I0000]
   ￮ constant id2ok defined
  
   ￫ info[I0000]
   ￮ constant nidok defined
  
  {x₀ : A} {x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B x₂ (f x₀) (g x₁)
    : Type
  
  {x₀₀ : A} {x₀₁ : A} {x₀₂ : Id A x₀₀ x₀₁} {x₁₀ : A} {x₁₁ : A}
  {x₁₂ : Id A x₁₀ x₁₁} {x₂₀ : Id A x₀₀ x₁₀} {x₂₁ : Id A x₀₁ x₁₁}
  (x₂₂ : A⁽ᵉᵉ⁾ x₀₂ x₁₂ x₂₀ x₂₁)
  →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ x₂₂ (f02 x₀₂) (f12 x₁₂) (f20 x₂₀) (f21 x₂₁)
    : Type
  
  (x : Id A) ⇒ Id B x.2
    : Type⁽ᵉ⁾ ((x : A) → B x) ((x : A) → B x)
  

  $ narya higherpi.ny -e "echo (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0702]
   ￭ command-line exec string
   1 | echo (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ unexpected explicit domain: all boundary domains must be implicit and primary domain explicit
  
  [1]

  $ narya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
  {x₀ : A} {x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B x₂ (f x₀) (g x₁)
    : Type
  

  $ narya higherpi.ny -e "echo {x₀ x₁ : A} {x₂ : refl A x₀ x₁} →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0702]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} {x₂ : refl A x₀ x₁} →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ unexpected implicit domain: all boundary domains must be implicit and primary domain explicit
  
  [1]

  $ narya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : refl (B x₀) (f x₀) (f x₀)) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : refl (B x₀) (f x₀) (f x₀)) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ invalid higher function-type: invalid domain scope
  
  [1]

  $ narya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : A) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : A) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ invalid higher function-type: invalid domain
  
  [1]

  $ narya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : Id A x₀ x₀) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : Id A x₀ x₀) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ invalid higher function-type: invalid domain boundary
  
  [1]

  $ narya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl (B x₀) (f x₀) (g x₀)"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl (B x₀) (f x₀) (g x₀)
     ^ invalid higher function-type: invalid codomain scope
  
  [1]

  $ narya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ A"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ A
     ^ invalid higher function-type: invalid codomain
  
  [1]

  $ narya higherpi.ny -e "echo (x : Id A) ⇒ A"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo (x : Id A) ⇒ A
     ^ invalid higher function-type: invalid single codomain dimension
  
  [1]
