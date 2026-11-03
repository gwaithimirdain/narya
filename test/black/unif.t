Placeholders "_" in term positions create unification metavariables.  Any command that leaves one unsolved fails.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a : A
  > def x : A ≔ _
  > def f (y : _) : A ≔ a
  > def g (y : A) : A ≔ match y [ _ ↦ _ ]
  > echo (_ : A)
  > def ok : A ≔ a
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ info[I0000]
   ￮ constant ok defined
  
  [1]

A unification metavariable whose environment is a weakened identity can be solved by comparing it with a value in its context.  Solved metavariables are displayed as their solutions, during and after the command that solves them.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a : A
  > def id (X : Type) (x : X) : X ≔ x
  > def t : A ≔ id _ a
  > synth id _ a
  > echo id _ a
  > def t' : A ≔ t
  > about t
  > def P (Q : Type → Type) (q : Q _) : Q A ≔ q
  > def u (B : Type) (b : B) : B ≔ let X : Type ≔ _ in id X b
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant id defined
  
   ￫ info[I0000]
   ￮ constant t defined
  
  id A a
    : A
  
  a
    : A
  
   ￫ info[I0000]
   ￮ constant t' defined
  
  id A a
    : A
  
   ￫ info[I0000]
   ￮ constant P defined
  
   ￫ info[I0000]
   ￮ constant u defined
  

Unification works inside let-bound values, whether or not they are case trees.

  $ narya -v - <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def u (B : Type) (b : B) : B ≔ let X : Type ≔ _ in let y : X ≔ b in y
  > def v (B : Type) (b : B) (c : Bool) : B ≔ let X : Type ≔ _ in let y : X ≔ match (c : Bool) [ true. ↦ b | false. ↦ b ] in y
  > EOF
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant u defined
  
   ￫ info[I0000]
   ￮ constant v defined
  

A case tree stuck on an unsolved metavariable is blocked, and is recomputed once the metavariable is solved, even if its blocked value has been computed and cached in the meantime.  Here the type Z, i.e. T ?u, is forced while ?u is unsolved, by comparing two terms of type Z; then ?u is solved by comparing b with true., after which Z must compute to ℕ.

  $ narya -v - <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def T (b : Bool) : Type ≔ match b [ true. ↦ ℕ | false. ↦ Bool ]
  > def id (X : Type) (x : X) : X ≔ x
  > def test : ℕ ≔ let b : Bool ≔ _ in let Z : Type ≔ T b in let z : Z ≔ _ in let e : Id Z z (id Z z) ≔ refl z in let w : Id Bool b true. ≔ refl (true. : Bool) in let k : Id ℕ z zero. ≔ refl (zero. : ℕ) in suc. z
  > echo test
  > EOF
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant id defined
  
   ￫ info[I0000]
   ￮ constant test defined
  
  1
    : ℕ
  

An ascribed type is checked speculatively.  A metavariable created inside a speculation that succeeds can be solved outside it afterwards.  But a speculation can't solve a metavariable created outside it, since if the speculation were backtracked, values created outside it might retain consequences of the solution.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a : A
  > def id (X : Type) (x : X) : X ≔ x
  > def s : A ≔ (a : _)
  > def s' : A ≔ let X : Type ≔ _ in (a : id X A)
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant id defined
  
   ￫ info[I0000]
   ￮ constant s defined
  
   ￫ error[E0401]
   ￭ stdin
   5 | def s' : A ≔ let X : Type ≔ _ in (a : id X A)
     ^ term synthesized type
         Type
       but is being checked against type
         X
       unequal head terms:
         Type
       does not equal
         X
  
   ￫ error[E0401]
   ￭ stdin
   5 | def s' : A ≔ let X : Type ≔ _ in (a : id X A)
     ^ term synthesized type
         X
       but is being checked against type
         Type
       unequal head terms:
         X
       does not equal
         Type
  
  [1]

A metavariable can be solved in an extended context, by a value not involving the extra variables.  But it can't be solved by a value involving them, or by a value containing itself, including through a let-bound variable.

  $ narya -v - <<EOF
  > axiom F : Type → Type
  > axiom Q : Type → Type
  > axiom q : (X : Type) → Q (F X)
  > def weaken (A : Type) (a : A) (k : (X : Type) → ((Y : Type) → Y → X) → Type) : Type ≔ k _ (Y y ↦ a)
  > def strengthen (k : (X : Type) → ((Y : Type) → Y → X) → Type) : Type ≔ k _ (Y y ↦ y)
  > def occurs (k : (X : Type) → (Q X → Q (F X)) → Type) : Type ≔ k _ (y ↦ y)
  > def occurs_let : Type ≔ let X : Type ≔ _ in let w : Q X ≔ q X in X
  > EOF
   ￫ info[I0001]
   ￮ axiom F assumed
  
   ￫ info[I0001]
   ￮ axiom Q assumed
  
   ￫ info[I0001]
   ￮ axiom q assumed
  
   ￫ info[I0000]
   ￮ constant weaken defined
  
   ￫ error[E0401]
   ￭ stdin
   5 | def strengthen (k : (X : Type) → ((Y : Type) → Y → X) → Type) : Type ≔ k _ (Y y ↦ y)
     ^ term synthesized type
         Y
       but is being checked against type
         ?u1
       unequal head terms:
         Y
       does not equal
         ?u1
  
   ￫ error[E0401]
   ￭ stdin
   6 | def occurs (k : (X : Type) → (Q X → Q (F X)) → Type) : Type ≔ k _ (y ↦ y)
     ^ term synthesized type
         Q ?u2
       but is being checked against type
         Q (F ?u2)
       unequal head terms:
         ?u2
       does not equal
         F
  
   ￫ error[E0401]
   ￭ stdin
   7 | def occurs_let : Type ≔ let X : Type ≔ _ in let w : Q X ≔ q X in X
     ^ term synthesized type
         Q (F X)
       but is being checked against type
         Q X
       unequal head terms:
         F
       does not equal
         X
  
  [1]

A unification metavariable whose environment is not a weakened identity can't be solved yet.  This includes one used in a branch of a match against a variable, since the variable is substituted by a constructor there.  It is equal only to itself, and is displayed by number.

  $ narya -v - <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def v (B : Type) (b : B) (c : Bool) : B ≔ let X : Type ≔ _ in let y : X ≔ match c [ true. ↦ b | false. ↦ b ] in y
  > axiom A : Type
  > axiom B : A → Type
  > def F (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
  > display let ≔ environments
  > def F' (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
  > def H (a : A) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a → G a ≔ y ↦ y in A
  > EOF
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ error[E0401]
   ￭ stdin
   2 | def v (B : Type) (b : B) (c : Bool) : B ≔ let X : Type ≔ _ in let y : X ≔ match c [ true. ↦ b | false. ↦ b ] in y
     ^ term synthesized type
         B
       but is being checked against type
         X
       unequal head terms:
         B
       does not equal
         X
  
   ￫ error[E0401]
   ￭ stdin
   2 | def v (B : Type) (b : B) (c : Bool) : B ≔ let X : Type ≔ _ in let y : X ≔ match c [ true. ↦ b | false. ↦ b ] in y
     ^ term synthesized type
         B
       but is being checked against type
         X
       unequal head terms:
         B
       does not equal
         X
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ error[E0401]
   ￭ stdin
   5 | def F (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ term synthesized type
         B a
       but is being checked against type
         B (let only … in ?u1)
       unequal head terms:
         a
       does not equal
         let only … in ?u1
  
   ￫ info[I0101]
   ￮ display set let to environments
  
   ￫ error[E0401]
   ￭ stdin
   7 | def F' (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ term synthesized type
         B a
       but is being checked against type
         B (let only a : A ≔ a and b : B a ≔ b and x : A ≔ a in ?u2)
       unequal head terms:
         a
       does not equal
         let only a : A ≔ a and b : B a ≔ b and x : A ≔ a in ?u2
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
  [1]
