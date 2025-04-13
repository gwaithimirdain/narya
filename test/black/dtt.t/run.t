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
  
  Gel⁽ᵈ⁾ A (Gel A (y ↦ eq A a₀ y)) (y ↦ eq A a₁ y)
    (y ⤇ eq⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) a₁ a₀₁ y.0 y.1) a₂ a₀₂ a₁₂
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
  
  Gel⁽ᵈᵈ⁾ A (Gel A (y ↦ eq A a₀ y)) (Gel A (y ↦ eq A a₁ y))
    (Gel⁽ᵈ⁾ A (Gel A (y ↦ eq A a₀ y)) (y ↦ eq A a₁ y)
       (y ⤇ eq⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) a₁ a₀₁ y.0 y.1)) (y ↦ eq A a₂ y)
    (y ⤇ eq⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) a₂ a₀₂ y.0 y.1)
    (y ⤇ eq⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₁ y0)) a₂ a₁₂ y.0 y.1)
    (y ⤇
     eq⁽ᵈᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) (Gel A (y0 ↦ eq A a₁ y0))
       (Gel⁽ᵈ⁾ A (Gel A (y0 ↦ eq A a₀ y0)) (y0 ↦ eq A a₁ y0)
          (y0 ⤇ eq⁽ᵈ⁾ A (Gel A (y1 ↦ eq A a₀ y1)) a₁ a₀₁ y0.0 y0.1)) a₂ a₀₂ a₁₂
       a₀₁₂ y.00 y.01 y.10 y.11) a₃ a₀₃ a₁₃ a₀₁₃ a₂₃ a₀₂₃ a₁₂₃
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
   ￮ constant ASST defined
  
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
  
  $ narya -arity 2 -direction p -external -v sct.ny
   ￫ info[I0000]
   ￮ constant SCT defined
  
   ￫ info[I0000]
   ￮ constant 0s defined
  
   ￫ info[I0000]
   ￮ constant 1s defined
  
   ￫ info[I0000]
   ￮ constant 2s defined
  
  $ narya -dtt -e "def foo (X:Type) : Type^^(d) X := X^^(d)"
   ￫ error[E0310]
   ￭ command-line exec string
   1 | def foo (X:Type) : Type^^(d) X := X^^(d)
     ^ variable not available inside external degeneracy
  
  [1]

Can't take external degeneracies of axioms.

  $ narya -dtt -v -e "axiom A : Type" -e "echo A⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ error[E0311]
   ￭ command-line exec string
   1 | echo A⁽ᵈ⁾
     ^ constant A uses nonparametric axioms, can't appear inside an external degeneracy
  
  [1]

Or of anything that uses an axiom.

  $ narya -dtt -v -e "axiom A : Type def f : A → A ≔ x ↦ x echo f⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ error[E0311]
   ￭ command-line exec string
   1 | axiom A : Type def f : A → A ≔ x ↦ x echo f⁽ᵈ⁾
     ^ constant f uses nonparametric axioms, can't appear inside an external degeneracy
  
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

  $ narya -dtt -v -e "axiom A:Type def f : Type := A and g : Type := sig () echo g⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constants defined mutually:
       f
       g
  
   ￫ error[E0311]
   ￭ command-line exec string
   1 | axiom A:Type def f : Type := A and g : Type := sig () echo g⁽ᵈ⁾
     ^ constant g uses nonparametric axioms, can't appear inside an external degeneracy
  
  [1]

When a constant is defined containing a hole, it is allowed to be parametric, but then the hole cannot be filled by any term that uses an axiom.

  $ narya -dtt -v -fake-interact "axiom A:Type def B:Type := ? echo B⁽ᵈ⁾ solve 0 := A"
   ￫ info[I0001]
   ￮ axiom A assumed
  
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
   1 | axiom A:Type def B:Type := ? echo B⁽ᵈ⁾ solve 0 := A
     ^ constant A uses nonparametric axioms, can't be used in a parametric definition
  
