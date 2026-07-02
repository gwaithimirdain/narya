The nonparametric comonad mode theory currently requires -parametric.

  $ narya -nonparametric-comonad nonparametric.ny
  -nonparametric-comonad currently requires -parametric
  [1]

The comonad structure typechecks.

  $ narya -v -parametric -nonparametric-comonad nonparametric.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant ♭T defined
  
   ￫ info[I0000]
   ￮ constant ♭map defined
  
   ￫ info[I0000]
   ￮ constant ε defined
  
   ￫ info[I0000]
   ￮ constant △ defined
  
   ￫ info[I0000]
   ￮ constant T defined
  

Using a ♭-locked variable without a key requires the counit key.

  $ narya -parametric -nonparametric-comonad nonparametric.ny -e "def g (A : Type) (x : A) : A ≔ f A x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def g (A : Type) (x : A) : A ≔ f A x
     ^ use of id variable behind ♭ lock requires a key
  
  [1]

The reflexivity of the *modal* family ♭T has a *filtered* domain: instead of the
usual square of arguments, it takes a single (A :♭| Type), because ♭ removes the
parametric dimension.

  $ narya -parametric -nonparametric-comonad nonparametric.ny -e "echo refl ♭T"
  Id ♭T
    : (A :♭| Type) →⁽ᵉ⁾ Type⁽ᵉ⁾ (♭T A) (♭T A)
  

By contrast, the reflexivity of the *non-modal* family T has the usual full
square domain {A₀} {A₁} (A₂).

  $ narya -parametric -nonparametric-comonad nonparametric.ny -e "echo refl T"
  Id T
    : {A₀ : Type} {A₁ : Type} (A₂ : Type⁽ᵉ⁾ A₀ A₁) →⁽ᵉ⁾ Type⁽ᵉ⁾ (T A₀) (T A₁)
  

The filtered reflexivity computes correctly when applied to an argument.

  $ narya -parametric -nonparametric-comonad nonparametric.ny -e "echo refl ♭T Type"
  ♭T⁽ᵉ⁾ Type
    : Type⁽ᵉ⁾ (♭T Type) (♭T Type)
  

The filtered higher pi-type can be written explicitly, and refl ♭T checks
against it.

  $ narya -v -parametric -nonparametric-comonad nonparametric.ny -e "def rT : (A :♭| Type) →⁽ᵉ⁾ Type⁽ᵉ⁾ (♭T A) (♭T A) ≔ refl ♭T"
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant ♭T defined
  
   ￫ info[I0000]
   ￮ constant ♭map defined
  
   ￫ info[I0000]
   ￮ constant ε defined
  
   ￫ info[I0000]
   ￮ constant △ defined
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant rT defined
  

Iterated reflexivity keeps the filtered single-variable domain.

  $ narya -parametric -nonparametric-comonad nonparametric.ny -e "echo refl (refl ♭T)"
  ♭T⁽ᵉᵉ⁾
    : (A :♭| Type) →⁽ᵉᵉ⁾ Type⁽ᵉᵉ⁾ (♭T⁽ᵉ⁾ A) (♭T⁽ᵉ⁾ A) (♭T⁽ᵉ⁾ A) (♭T⁽ᵉ⁾ A)
  
