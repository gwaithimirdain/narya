Higher coinductive types with filtering-modal (♭) parameters: the ♭ parameter is
not degenerated in the contexts of higher fields, so field types can refer to it
directly, and its instances construct and project as expected.

  $ narya -v -parametric -discrete-coreflector nphct.ny
   ￫ info[I0000]
   ￮ constant ♭√ defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom s0 assumed
  
   ￫ info[I0001]
   ￮ axiom s1 assumed
  
   ￫ info[I0001]
   ￮ axiom s2 assumed
  
  s2 .root
    : A
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant √a defined
  
  a
    : A
  
   ￫ info[I0000]
   ￮ constant ♭√√ defined
  
   ￫ info[I0000]
   ￮ constant √√a defined
  
  a
    : A
  

Without the modality, an ordinary parameter IS degenerated in the higher field's
context, so the same field type fails to check: the parameter A becomes a square
of type Type⁽ᵉ⁾ A.0 A.1, which is not a Type.

  $ narya -parametric -discrete-coreflector -e "def sqrt (A : Type) : Type ≔ codata [ x .root.e : A ]"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def sqrt (A : Type) : Type ≔ codata [ x .root.e : A ]
     ^ term synthesized type
         Type⁽ᵉ⁾ A.0 A.1
       but is being checked against type
         Type
       unequal head terms:
         Type⁽ᵉ⁾
       does not equal
         Type
  
  [1]

  $ narya -v -parametric -discrete-coreflector -direction p,rel,Br param_sqrt.ny
   ￫ info[I0000]
   ￮ constant √ defined
  

