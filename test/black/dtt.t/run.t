  $ narya -dtt -v sst.ny
   ￫ info[I0000]
   ￮ constant Gel defined
  
   ￫ info[I0000]
   ￮ constant SST defined
  
   ￫ info[I0000]
   ￮ constant 0s defined
  
   ￫ info[I0000]
   ￮ constant 1s defined
  
   ￫ info[I0000]
   ￮ constant 2s defined
  
   ￫ info[I0000]
   ￮ constant 3s defined
  
   ￫ info[I0000]
   ￮ constant eq defined
  
   ￫ info[I0000]
   ￮ constant Sing defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
  A
    : Type
  
   ￫ info[I0001]
   ￮ axiom a₀ assumed
  
   ￫ info[I0001]
   ￮ axiom a₁ assumed
  
  Gel A (y ↦ eq A a₀ y) a₁
    : Type
  
   ￫ info[I0001]
   ￮ axiom a₀₁ assumed
  
   ￫ info[I0001]
   ￮ axiom a₂ assumed
  
   ￫ info[I0001]
   ￮ axiom a₀₂ assumed
  
   ￫ info[I0001]
   ￮ axiom a₁₂ assumed
  
  Gel⁽ᵈ⁾ (Gel A (y ↦ eq A a₀ y)) {y ↦ eq A a₁ y}
    (y ⤇ eq⁽ᵈ⁾ (Gel A (y′ ↦ eq A a₀ y′)) a₀₁ y.1) a₀₂ a₁₂
    : Type
  
   ￫ info[I0001]
   ￮ axiom a₀₁₂ assumed
  
   ￫ info[I0001]
   ￮ axiom a₃ assumed
  
   ￫ info[I0001]
   ￮ axiom a₀₃ assumed
  
   ￫ info[I0001]
   ￮ axiom a₁₃ assumed
  
   ￫ info[I0001]
   ￮ axiom a₀₁₃ assumed
  
   ￫ info[I0001]
   ￮ axiom a₂₃ assumed
  
   ￫ info[I0001]
   ￮ axiom a₀₂₃ assumed
  
   ￫ info[I0001]
   ￮ axiom a₁₂₃ assumed
  
  Gel⁽ᵈᵈ⁾
    (Gel⁽ᵈ⁾ (Gel A (y ↦ eq A a₀ y)) {y ↦ eq A a₁ y}
       (y ⤇ eq⁽ᵈ⁾ (Gel A (y′ ↦ eq A a₀ y′)) a₀₁ y.1)) {y ↦ eq A a₂ y}
    {y ⤇ eq⁽ᵈ⁾ (Gel A (y′ ↦ eq A a₀ y′)) a₀₂ y.1}
    {y ⤇ eq⁽ᵈ⁾ (Gel A (y′ ↦ eq A a₁ y′)) a₁₂ y.1}
    (y ⤇
     eq⁽ᵈᵈ⁾
       (Gel⁽ᵈ⁾ (Gel A (y′ ↦ eq A a₀ y′)) {y′ ↦ eq A a₁ y′}
          (y′ ⤇ eq⁽ᵈ⁾ (Gel A (y″ ↦ eq A a₀ y″)) a₀₁ y′.1)) a₀₁₂ y.11) a₀₁₃
    a₀₂₃ a₁₂₃
    : Type
  
   ￫ info[I0000]
   ￮ constant sst.∅ defined
  
   ￫ info[I0000]
   ￮ constant sst.𝟙 defined
  
   ￫ info[I0000]
   ￮ constant sst.prod defined
  
   ￫ info[I0000]
   ￮ constant sst.Σ defined
  
   ￫ info[I0000]
   ￮ constant sst.const defined
  
   ￫ info[I0000]
   ￮ constant sst.sum defined
  
   ￫ info[I0000]
   ￮ constant sst.discprod defined
  
   ￫ info[I0000]
   ￮ constant ASST defined
  
   ￫ info[I0000]
   ￮ constant asst.Int defined
  
   ￫ info[I0000]
   ￮ constant asst.Fib defined
  
   ￫ info[I0000]
   ￮ constant sst.Fib defined
  
   ￫ info[I0000]
   ￮ constant sst.Fib′ defined
  
   ￫ info[I0000]
   ￮ constant sst.pt defined
  
   ￫ info[I0000]
   ￮ constant sst.hom defined
  
   ￫ info[I0000]
   ￮ constant sst.id defined
  
   ￫ info[I0000]
   ￮ constant sst.comp defined
  
   ￫ info[I0000]
   ￮ constant sst.abort defined
  
   ￫ info[I0000]
   ￮ constant sst.uniq defined
  
   ￫ info[I0000]
   ￮ constant sst.pair defined
  
   ￫ info[I0000]
   ￮ constant sst.abortz defined
  
   ￫ info[I0000]
   ￮ constant sst.const_abort defined
  
   ￫ info[I0000]
   ￮ constant sst.copair defined
  

  $ narya -parametric -arity 2 -direction p -v sct.ny
   ￫ info[I0000]
   ￮ constant SCT defined
  
   ￫ info[I0000]
   ￮ constant 0s defined
  
   ￫ info[I0000]
   ￮ constant 1s defined
  
   ￫ info[I0000]
   ￮ constant 2s defined
  
  $ narya -dtt -e "def foo (X:Type) : Type^^(d) X := X^^(d)"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def foo (X:Type) : Type^^(d) X := X^^(d)
     ^ use of id variable behind △□ lock requires a key
  
  [1]

Can't take external degeneracies of nonparametric axioms.

  $ narya -dtt -v -e "axiom #(nonparametric) A : Type" -e "echo A⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ nonparametric axiom A assumed
  
   ￫ error[E0311]
   ￭ command-line exec string
   1 | echo A⁽ᵈ⁾
     ^ constant A is or uses a nonparametric axiom, can't appear inside an external degeneracy
  
  [1]

Or of anything that uses a nonparametric axiom.

  $ narya -dtt -v -e "axiom #(nonparametric) A : Type def f : A → A ≔ x ↦ x echo f⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ nonparametric axiom A assumed
  
   ￫ info[I0000]
   ￮ nonparametric constant f defined
  
   ￫ error[E0311]
   ￭ command-line exec string
   1 | axiom #(nonparametric) A : Type def f : A → A ≔ x ↦ x echo f⁽ᵈ⁾
     ^ constant f is or uses a nonparametric axiom, can't appear inside an external degeneracy
  
  [1]

All axioms using a nonparametric axiom must also be nonparametric

  $ narya -dtt -v -e "axiom #(nonparametric) A : Type axiom #(nonparametric) a : A axiom a' : A"
   ￫ info[I0001]
   ￮ nonparametric axiom A assumed
  
   ￫ info[I0001]
   ￮ nonparametric axiom a assumed
  
   ￫ error[E0312]
   ￭ command-line exec string
   1 | axiom #(nonparametric) A : Type axiom #(nonparametric) a : A axiom a' : A
     ^ constant A is or uses a nonparametric axiom, can't be used in a parametric command
  
  [1]


We check that a family of mutual definitions can apply external degeneracies to each other.  This was an issue once because they are temporarily defined as "axioms" during definition, and by default axioms don't admit external degeneracies.

  $ narya -dtt -v -e "def X : Type ≔ Type and Y : (x : X) → X⁽ᵈ⁾ x ≔ ?"
   ￫ info[I0000]
   ￮ constants defined mutually, containing 1 hole:
       X
       Y
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     (x : Type) → Type⁽ᵈ⁾ x
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

But if one of them uses an axiom, the others don't have external degeneracies either.

  $ narya -dtt -v -e "axiom #(nonparametric) A:Type def f : Type := A and g : Type := sig () echo g⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ nonparametric axiom A assumed
  
   ￫ info[I0000]
   ￮ nonparametric constants defined mutually:
       f
       g
  
   ￫ error[E0311]
   ￭ command-line exec string
   1 | axiom #(nonparametric) A:Type def f : Type := A and g : Type := sig () echo g⁽ᵈ⁾
     ^ constant g is or uses a nonparametric axiom, can't appear inside an external degeneracy
  
  [1]

When a constant is defined containing a hole, it is allowed to be parametric, but then the hole cannot be filled by any term that uses an axiom.

  $ narya -dtt -v -fake-interact "axiom #(nonparametric) A:Type def B:Type := ? echo B⁽ᵈ⁾ solve 0 := A"
   ￫ info[I0001]
   ￮ nonparametric axiom A assumed
  
   ￫ info[I0000]
   ￮ constant B defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Type
  
  B⁽ᵈ⁾
    : Type⁽ᵈ⁾ B
  
   ￫ error[E0312]
   ￭ command line fake-interact
   1 | axiom #(nonparametric) A:Type def B:Type := ? echo B⁽ᵈ⁾ solve 0 := A
     ^ constant A is or uses a nonparametric axiom, can't be used in a parametric command
  

General displayed coinductives

  $ narya -dtt -v dcoind.ny
   ￫ info[I0000]
   ￮ constant disp defined
  
   ￫ info[I0000]
   ￮ constant dCoind defined
  

  $ narya -dtt -v discrete.ny
   ￫ info[I0000]
   ￮ constant disp defined
  
   ￫ info[I0000]
   ￮ constant eq defined
  
   ￫ info[I0000]
   ￮ constant △ defined
  
   ￫ info[I0000]
   ￮ constant □ defined
  
   ￫ info[I0000]
   ￮ constant △□ defined
  
   ￫ info[I0000]
   ￮ constant △ᵈ defined
  
   ￫ info[I0000]
   ￮ constant △ᵈ_eq defined
  
   ￫ info[I0000]
   ￮ constant △□ᵈ defined
  
   ￫ info[I0000]
   ￮ constant △□ᵈ_eq defined
  
   ￫ info[I0000]
   ￮ constant ◇ defined
  
   ￫ info[I0000]
   ￮ constant △◇ defined
  
   ￫ info[I0000]
   ￮ constant △◇ᵈ defined
  
   ￫ info[I0000]
   ￮ constant △◇ᵈ_eq defined
  

  $ narya -v -dtt higher-display.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constants defined mutually:
       ∂
       d
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant ∂0 defined
  
   ￫ info[I0000]
   ￮ constant d0 defined
  
   ￫ info[I0000]
   ￮ constant ∂1 defined
  
   ￫ info[I0000]
   ￮ constant d1 defined
  
   ￫ info[I0000]
   ￮ constant ∂2 defined
  
   ￫ info[I0000]
   ￮ constant d2 defined
  
   ￫ info[I0000]
   ￮ constant ∂3 defined
  
   ￫ info[I0000]
   ￮ constant d3 defined
  
