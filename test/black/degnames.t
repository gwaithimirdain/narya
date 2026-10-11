This tests the "display degeneracy names" options, which control the dimension
up to which an iterated reflexivity is printed with iterated names like
"refl (refl x)" rather than with a superscript like "x⁽ᵉᵉ⁾".

  $ cat - >degnames.ny <<EOF
  > axiom A : Type
  > axiom a : A
  > axiom f : A → A
  > echo refl (refl a)
  > echo Id (Id A)
  > echo refl (refl f)
  > display other degeneracy names ≔ 2
  > echo refl (refl a)
  > echo Id (Id A)
  > echo refl (refl f)
  > display type degeneracy names ≔ 2
  > display function degeneracy names ≔ 2
  > echo refl (refl a)
  > echo Id (Id A)
  > echo refl (refl f)
  > EOF

  $ narya -fake-interact=degnames.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
  a⁽ᵉᵉ⁾
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
  A⁽ᵉᵉ⁾
    : Type⁽ᵉᵉ⁾ (Id A) (Id A) (Id A) (Id A)
  
  f⁽ᵉᵉ⁾
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ (ap f 𝑥₀₂) (ap f 𝑥₁₂) (ap f 𝑥₂₀) (ap f 𝑥₂₁)
  
   ￫ info[I0101]
   ￮ display set other degeneracy names to 2
  
  refl (refl a)
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
  A⁽ᵉᵉ⁾
    : Type⁽ᵉᵉ⁾ (Id A) (Id A) (Id A) (Id A)
  
  f⁽ᵉᵉ⁾
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : A⁽ᵉᵉ⁾ 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ (ap f 𝑥₀₂) (ap f 𝑥₁₂) (ap f 𝑥₂₀) (ap f 𝑥₂₁)
  
   ￫ info[I0101]
   ￮ display set type degeneracy names to 2
  
   ￫ info[I0101]
   ￮ display set function degeneracy names to 2
  
  refl (refl a)
    : Id (Id A) (refl a) (refl a) (refl a) (refl a)
  
  Id (Id A)
    : Type⁽ᵉᵉ⁾ (Id A) (Id A) (Id A) (Id A)
  
  ap (ap f)
    : {𝑥₀₀ : A} {𝑥₀₁ : A} {𝑥₀₂ : Id A 𝑥₀₀ 𝑥₀₁} {𝑥₁₀ : A} {𝑥₁₁ : A}
      {𝑥₁₂ : Id A 𝑥₁₀ 𝑥₁₁} {𝑥₂₀ : Id A 𝑥₀₀ 𝑥₁₀} {𝑥₂₁ : Id A 𝑥₀₁ 𝑥₁₁}
      (𝑥₂₂ : Id (Id A) 𝑥₀₂ 𝑥₁₂ 𝑥₂₀ 𝑥₂₁)
      →⁽ᵉᵉ⁾ Id (Id A) (ap f 𝑥₀₂) (ap f 𝑥₁₂) (ap f 𝑥₂₀) (ap f 𝑥₂₁)
  

The default value of each option is 1, so a 1-dimensional degeneracy gets a name
but higher ones get superscripts.  Setting an option to 0 removes the names
entirely, and setting it to a larger value uses names in higher dimensions.

  $ cat - >zero.ny <<EOF
  > axiom A : Type
  > axiom a : A
  > axiom f : A → A
  > display other degeneracy names ≔ 0
  > display type degeneracy names ≔ 0
  > display function degeneracy names ≔ 0
  > echo refl a
  > echo Id A
  > echo refl f
  > display other degeneracy names ≔ 3
  > echo refl (refl (refl a))
  > EOF

  $ narya -fake-interact=zero.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0101]
   ￮ display set other degeneracy names to 0
  
   ￫ info[I0101]
   ￮ display set type degeneracy names to 0
  
   ￫ info[I0101]
   ￮ display set function degeneracy names to 0
  
  a⁽ᵉ⁾
    : A⁽ᵉ⁾ a a
  
  A⁽ᵉ⁾
    : Type⁽ᵉ⁾ A A
  
  f⁽ᵉ⁾
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : A⁽ᵉ⁾ 𝑥₀ 𝑥₁) →⁽ᵉ⁾ A⁽ᵉ⁾ (f 𝑥₀) (f 𝑥₁)
  
   ￫ info[I0101]
   ￮ display set other degeneracy names to 3
  
  refl (refl (refl a))
    : A⁽ᵉᵉᵉ⁾ (refl (refl a)) (refl (refl a)) (refl (refl a)) (refl (refl a))
        (refl (refl a)) (refl (refl a))
  

Symmetries are unaffected, as are canonical types, which always print with a
superscript.

  $ cat - >sym.ny <<EOF
  > def Prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )
  > axiom A : Type
  > axiom a : A
  > axiom b : A
  > axiom p : Id A a b
  > display other degeneracy names ≔ 3
  > display type degeneracy names ≔ 3
  > echo sym (refl p)
  > echo Id (Id (Prod A A))
  > EOF

  $ narya -fake-interact=sym.ny
   ￫ info[I0000]
   ￮ constant Prod defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom p assumed
  
   ￫ info[I0101]
   ￮ display set other degeneracy names to 3
  
   ￫ info[I0101]
   ￮ display set type degeneracy names to 3
  
  p⁽ᵉ¹⁾
    : Id (Id A) p p (refl a) (refl b)
  
  Prod⁽ᵉᵉ⁾ (Id (Id A)) (Id (Id A))
    : Type⁽ᵉᵉ⁾ (Prod⁽ᵉ⁾ (Id A) (Id A)) (Prod⁽ᵉ⁾ (Id A) (Id A))
        (Prod⁽ᵉ⁾ (Id A) (Id A)) (Prod⁽ᵉ⁾ (Id A) (Id A))
  
