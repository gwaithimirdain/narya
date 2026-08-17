  $ narya -parametric -v holes.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
  B
    : Type
  
   ￫ info[I0000]
   ￮ constant id defined
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0001]
   ￮ axiom a_very_long_variable assumed
  
   ￫ info[I0001]
   ￮ axiom a_very_long_function assumed
  
   ￫ info[I0000]
   ￮ constant f' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0007]
   ￮ section sec opened
  
   ￫ info[I0002]
   ￮ notation «&» defined
  
   ￫ info[I0000]
   ￮ constant f' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?2:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0008]
   ￮ section sec closed
  
   ￫ info[I0002]
   ￮ notation «$» defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant plus defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?3:
     
     m : ℕ
     n ≔ 0 : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I3003]
   ￮ hole ?4:
     
     m : ℕ
     n : ℕ
     n′ ≔ suc. n : ℕ (not in scope)
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0001]
   ￮ axiom P assumed
  
   ￫ info[I0000]
   ￮ constant anop defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?5:
     
     n″ : ℕ (not in scope)
     n′ : ℕ
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?6:
     
     n′ : ℕ
     n″ : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop'' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?7:
     
     n′ : ℕ (not in scope)
     𝑥 : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop''' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?8:
     
     𝑥 : ℕ
     𝑦 : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0000]
   ￮ constant pp defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?9:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?10:
     
     ----------------------------------------------------------------------
     pp .fst
  
   ￫ info[I0000]
   ￮ constant pp' defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?11:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?12:
     
     ----------------------------------------------------------------------
     ?11{…}
  
   ￫ info[I0000]
   ￮ constant foo defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?13:
     
     bar : ℕ
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant foo' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?14:
     
     bar : Type
     x : bar
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel0 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?15:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel0 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel1 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?16:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel1 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel2 defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?17:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel2 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?18:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel2 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant gel3 defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?19:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel3 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?20:
     
     A : Type
     B : Type
     x.0 : A
     x.1 : B
     x.2 : gel3 A B x.0 x.1
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0000]
   ￮ constant AC defined
  
   ￫ info[I0000]
   ￮ constant ac defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?21:
     
     ----------------------------------------------------------------------
     ℕ → A
  
   ￫ info[I3003]
   ￮ hole ?22:
     
     ----------------------------------------------------------------------
     C (ac .a 0)
  
   ￫ info[I0000]
   ￮ constant ida defined
  
   ￫ info[I0000]
   ￮ constant ideqid defined
  
  {u} {u′} u″ ↦ u″
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id A 𝑥₀ 𝑥₁
  
   ￫ info[I0000]
   ￮ constant ideqid' defined
  
  {u} {u′} u′′ ↦ u′′
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id A 𝑥₀ 𝑥₁
  
   ￫ info[I0000]
   ￮ constant ideqid'' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?23:
     
     u″ : A (not in scope)
     u′ : A (not in scope)
     u : Id A u″ u′
     ----------------------------------------------------------------------
     Id A u″ u′
  
   ￫ info[I0000]
   ￮ constant afam defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?24:
     
     X : Type
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant idafam defined
  
   ￫ info[I0001]
   ￮ axiom f0 assumed
  
   ￫ info[I0000]
   ￮ constant f2 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?25:
     
     x.0 : A
     x.1 : A
     x.2 : Id A x.0 x.1
     ----------------------------------------------------------------------
     Id B (f0 x.0) (f0 x.1)
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant p defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?26:
     
     ----------------------------------------------------------------------
     prod
  
   ￫ info[I0001]
   ￮ axiom p0 assumed
  
   ￫ info[I0000]
   ￮ constant p2 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?27:
     
     ----------------------------------------------------------------------
     prod⁽ᵉ⁾ p0 p0
  
   ￫ info[I0000]
   ￮ constant prod' defined
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/holes.ny
   110 | def p : prod ≔ ?
       ^ previous definition
   116 | def p : prod' ≔ ?
       ^ redefining constant: p
  
   ￫ info[I0000]
   ￮ constant p defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?28:
     
     ----------------------------------------------------------------------
     prod'
  
   ￫ error[E3002]
   ￮ file holes.ny contains open holes
  
  [1]

  $ narya -v -dtt dtt-holes.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/dtt-holes.ny
   6 | def g (X : Type) : Type⁽ᵈ⁾ X ≔ (f ?)⁽ᵈ⁾
     ^ term synthesized type
         Type⁽ᵈ⁾ ?0{…}
       but is being checked against type
         Type⁽ᵈ⁾ X
       unequal head terms:
         ?0{…}
       does not equal
         X
  
  [1]

Holes in echo:

  $ narya -e 'echo (? : Type)'
  ?0{…}
    : Type
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

No holes in imported file

  $ echo 'def A : Type := ?' >to_import.ny

  $ narya -e 'import "to_import"'
   ￫ error[E2002]
   ￭ $TESTCASE_ROOT/to_import.ny
   1 | def A : Type := ?
     ^ imported file '$TESTCASE_ROOT/to_import.ny' cannot contain holes
  
  [1]
