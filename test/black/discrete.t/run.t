The nonparametric comonad mode theory currently requires -parametric.

  $ narya -discrete-coreflector discrete.ny
  -discrete-coreflector requires -parametric
  [1]

The comonad structure typechecks, and the modal type is parametrically trivial.

  $ narya -v -parametric -direction p,rel,Br -discrete-coreflector discrete.ny
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
   ￮ constant eq defined
  
   ￫ info[I0000]
   ￮ constant Br_♭T_trivial defined
  
   ￫ info[I0000]
   ￮ constant eqd defined
  
   ￫ info[I0000]
   ￮ constant Br_♭T_trivial2 defined
  

Using a ♭-locked variable without a key requires the counit key.

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "def g (A : Type) (x : A) : A ≔ f A x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def g (A : Type) (x : A) : A ≔ f A x
     ^ use of id variable behind ♭ lock requires a key
  
  [1]

The reflexivity of the *modal* family ♭T has a *filtered* domain: instead of the
usual square of arguments, it takes a single (A :♭| Type), because ♭ removes the
parametric dimension.

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "echo rel ♭T"
  Br ♭T
    : (A :♭| Type) →⁽ᵖ⁾ Type⁽ᵖ⁾ (♭T A) (♭T A)
  

By contrast, the reflexivity of the *non-modal* family T has the usual full
square domain {A₀} {A₁} (A₂).

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "echo rel T"
  Br T
    : {A₀ : Type} {A₁ : Type} (A₂ : Type⁽ᵖ⁾ A₀ A₁) →⁽ᵖ⁾ Type⁽ᵖ⁾ (T A₀) (T A₁)
  

The filtered reflexivity computes correctly when applied to an argument.

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "echo rel ♭T Type"
  ♭T⁽ᵖ⁾ Type
    : Type⁽ᵖ⁾ (♭T Type) (♭T Type)
  

The filtered higher pi-type can be written explicitly, and refl ♭T checks
against it.

  $ narya -v -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "def rT : (A :♭| Type) →⁽ᵖ⁾ Type⁽ᵖ⁾ (♭T A) (♭T A) ≔ rel ♭T"
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
   ￮ constant eq defined
  
   ￫ info[I0000]
   ￮ constant Br_♭T_trivial defined
  
   ￫ info[I0000]
   ￮ constant eqd defined
  
   ￫ info[I0000]
   ￮ constant Br_♭T_trivial2 defined
  
   ￫ info[I0000]
   ￮ constant rT defined
  

Iterated reflexivity keeps the filtered single-variable domain.

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "echo rel (rel ♭T)"
  ♭T⁽ᵖᵖ⁾
    : (A :♭| Type) →⁽ᵖᵖ⁾ Type⁽ᵖᵖ⁾ (♭T⁽ᵖ⁾ A) (♭T⁽ᵖ⁾ A) (♭T⁽ᵖ⁾ A) (♭T⁽ᵖ⁾ A)
  


Reflexivity of modal *lambdas* (not just constants) also reads back with a
filtered domain, and computes when applied.

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "echo rel ((A : ♭| Type) ↦ A)"
  A ↦ Br A
    : (A :♭| Type) →⁽ᵖ⁾ Type⁽ᵖ⁾ A A
  

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "echo rel ((A : ♭| Type) ↦ ♭T A)"
  A ↦ ♭T⁽ᵖ⁾ A
    : (A :♭| Type) →⁽ᵖ⁾ Type⁽ᵖ⁾ (♭T A) (♭T A)
  

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "echo rel ((A : ♭| Type) ↦ ♭T A) Type"
  ♭T⁽ᵖ⁾ Type
    : Type⁽ᵖ⁾ (♭T Type) (♭T Type)
  

  $ narya -parametric -direction p,rel,Br -discrete-coreflector discrete.ny -e "echo rel (rel ((A : ♭| Type) ↦ ♭T A))"
  A ↦ ♭T⁽ᵖᵖ⁾ A
    : (A :♭| Type) →⁽ᵖᵖ⁾ Type⁽ᵖᵖ⁾ (♭T⁽ᵖ⁾ A) (♭T⁽ᵖ⁾ A) (♭T⁽ᵖ⁾ A) (♭T⁽ᵖ⁾ A)
  

