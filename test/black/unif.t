Placeholders "_" in term positions create unification metavariables.  Any command that leaves one unsolved fails.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a : A
  > def x : A ≔ _
  > def f (y : _) : A ≔ a
  > def g (y : A) : A ≔ match y [ _ ↦ _ ]
  > echo (_ : A)
  > def ok : A ≔ a
  > echo x
  > def y (z : A) : A ≔ x
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
  
   ￫ info[I0000]
   ￮ constant y defined
  
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
  

A metavariable can also be solved when its environment is a renaming, sending the variables of its context to distinct variables of the current context, including permuting them, and including entire cubes of variables.  A let-bound variable in its context doesn't count, since its value is determined by the others.  Below, the normal forms show that the solutions are in terms of the metavariable's own variables.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom C : A → A → Type
  > def ren (h : (y : A) → B y) : A → Type ≔ let G : A → Type ≔ x ↦ B _ in y ↦ let k : G y ≔ h y in G y
  > def perm (h : (y z : A) → C z y) : A → A → Type ≔ let G : A → A → Type ≔ p q ↦ C _ _ in y z ↦ let k : G y z ≔ h y z in let j : G z y ≔ h z y in G y z
  > def letent (a : A) (h : (y : A) → B y) : A → Type ≔ let c : A ≔ a in let G : A → Type ≔ x ↦ B _ in y ↦ let k : G y ≔ h y in G y
  > def cub (f : A → Type) (Q : (y0 y1 : A) (y2 : Id A y0 y1) → Id Type (f y0) (f y1)) : (y0 y1 : A) (y2 : Id A y0 y1) → Id Type (f y0) (f y1) ≔ let G : Id (A → Type) f f ≔ x ⤇ Q _ _ _ in y0 y1 y2 ↦ let k : Id (Id Type (f y0) (f y1)) (G y2) (Q y0 y1 y2) ≔ refl (Q y0 y1 y2) in G y2
  > axiom a0 : A
  > axiom a1 : A
  > axiom a2 : Id A a0 a1
  > axiom h0 : (y : A) → B y
  > axiom hh : (y z : A) → C z y
  > axiom f0 : A → Type
  > axiom Q0 : (y0 y1 : A) (y2 : Id A y0 y1) → Id Type (f0 y0) (f0 y1)
  > about ren
  > echo ren h0 a0
  > echo perm hh a0 a1
  > echo letent a1 h0 a0
  > echo cub f0 Q0 a0 a1 a2
  > EOF
  h ↦ let G ≔ x ↦ B x in y ↦ let k ≔ h y in G y
    : (h : (y : A) → B y) → A → Type
  
  B a0
    : Type
  
  C a1 a0
    : Type
  
  B a0
    : Type
  
  Q0 a0 a1 a2
    : Type⁽ᵉ⁾ (f0 a0) (f0 a1)
  

But the value must not involve variables outside the image of the renaming.  And if the environment repeats a variable, the value can't use it, since then there would be more than one solution.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > def scope (h : (w : A) → B w) : A → A → Type ≔ let G : A → Type ≔ x ↦ B _ in y w ↦ let k : G y ≔ h w in A
  > def repeated (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
  > def repeated2 : A → Type ≔ let G : A → A → Type ≔ p q ↦ B _ in y ↦ let k : Id Type (G y y) (B y) ≔ refl (B y) in A
  > axiom K : Type → Type → Type
  > axiom kk : (X : Type) → K X X
  > def repeated3 : A → Type ≔ let G : A → A → Type ≔ p q ↦ K _ _ in y ↦ let k : G y y ≔ kk _ in A
  > EOF
   ￫ error[E0401]
   ￭ stdin
   3 | def scope (h : (w : A) → B w) : A → A → Type ≔ let G : A → Type ≔ x ↦ B _ in y w ↦ let k : G y ≔ h w in A
     ^ term synthesized type
         B w
       but is being checked against type
         B (let only … in ?u0)
       unequal head terms:
         w
       does not equal
         let only … in ?u0
  
   ￫ error[E0401]
   ￭ stdin
   4 | def repeated (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ term synthesized type
         B a
       but is being checked against type
         B (let only … in ?u1)
       unequal head terms:
         a
       does not equal
         let only … in ?u1
  
   ￫ error[E0401]
   ￭ stdin
   5 | def repeated2 : A → Type ≔ let G : A → A → Type ≔ p q ↦ B _ in y ↦ let k : Id Type (G y y) (B y) ≔ refl (B y) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B y) (B y)
       but is being checked against type
         Type⁽ᵉ⁾ (B (let only … in ?u2)) (B y)
       unequal head terms:
         y
       does not equal
         let only … in ?u2
  
   ￫ error[E0401]
   ￭ stdin
   8 | def repeated3 : A → Type ≔ let G : A → A → Type ≔ p q ↦ K _ _ in y ↦ let k : G y y ≔ kk _ in A
     ^ term synthesized type
         K (let only … in ?u3) (let only … in ?u3)
       but is being checked against type
         K (let only … in ?u3) (let only … in ?u4)
       unequal head metavariables:
         ?u3
       does not equal
         ?u4
  
  [1]

If the value doesn't use a repeated variable, then the solution is unique, since substituting variables for variables can't trigger any computation.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > def rep (b : A) : A → Type ≔ let G : A → A → Type ≔ p q ↦ _ in y ↦ let k : Id Type (G y y) (B b) ≔ refl (B b) in G y y
  > axiom a0 : A
  > axiom a1 : A
  > echo rep a0 a1
  > EOF
  B a0
    : Type
  

But the solution must still be well-typed, so it can't be solved if the type of the metavariable depends on a repeated variable, nor can it use a variable whose type does.  Below, the type of the first metavariable would be X → Y → Y, while in the second the solution would be e c with c : X and e : Y → Type.

  $ narya - <<EOF
  > def tydep : (Z : Type) → Type ≔ let m : (X Y : Type) → X → Y → Y ≔ X Y ↦ _ in Z ↦ let k : Id (Z → Z → Z) (m Z Z) ((x y ↦ y) : Z → Z → Z) ≔ refl ((x y ↦ y) : Z → Z → Z) in Z
  > def vardep : (Z : Type) (z : Z) (e : Z → Type) → Type ≔ let G : (X Y : Type) (c : X) (e : Y → Type) → Type ≔ X Y c e ↦ _ in Z z e ↦ let k : Id Type (G Z Z z e) (e z) ≔ refl (e z) in Type
  > EOF
   ￫ error[E0401]
   ￭ stdin
   1 | def tydep : (Z : Type) → Type ≔ let m : (X Y : Type) → X → Y → Y ≔ X Y ↦ _ in Z ↦ let k : Id (Z → Z → Z) (m Z Z) ((x y ↦ y) : Z → Z → Z) ≔ refl ((x y ↦ y) : Z → Z → Z) in Z
     ^ term synthesized type
         {𝑥₀ : Z} {𝑥₁ : Z} (𝑥₂ : Id Z 𝑥₀ 𝑥₁) {𝑦₀ : Z} {𝑦₁ : Z} (𝑦₂ : Id Z 𝑦₀ 𝑦₁)
         →⁽ᵉ⁾ Id Z 𝑦₀ 𝑦₁
       but is being checked against type
         {𝑥₀ : Z} {𝑥₁ : Z} (𝑥₂ : Id Z 𝑥₀ 𝑥₁) {𝑦₀ : Z} {𝑦₁ : Z} (𝑦₂ : Id Z 𝑦₀ 𝑦₁)
         →⁽ᵉ⁾ Id Z ((let only … in ?u0) 𝑥₀ 𝑦₀) 𝑦₁
       unequal head terms:
         𝑦
       does not equal
         let only … in ?u0
  
   ￫ error[E0401]
   ￭ stdin
   2 | def vardep : (Z : Type) (z : Z) (e : Z → Type) → Type ≔ let G : (X Y : Type) (c : X) (e : Y → Type) → Type ≔ X Y c e ↦ _ in Z z e ↦ let k : Id Type (G Z Z z e) (e z) ≔ refl (e z) in Type
     ^ term synthesized type
         Type⁽ᵉ⁾ (e z) (e z)
       but is being checked against type
         Type⁽ᵉ⁾ (let only … in ?u1) (e z)
       unequal head terms:
         e
       does not equal
         let only … in ?u1
  
  [1]

A renaming can send variables with a modal annotation to variables with the same annotation, and can pass through matching locks.  The value can use the variables with keys, or under locks that it introduces itself.  If a variable has a different annotation than the one it renames, the value can't use it (see below), but it can be solved by a value that doesn't.

  $ narya -spatial - <<EOF
  > axiom A : Type
  > axiom B : (_ :♭| A) → Type
  > axiom C : A → Type
  > axiom D : (_ :♭| Type) → Type
  > axiom a0 : A
  > axiom b0 : (y :♭| A) → B y
  > axiom c0 : (y :♭| A) → C y
  > def locked (h : (y :♭| A) → B y) : (y :♭| A) → Type ≔ let G : (_ :♭| A) → Type ≔ x ↦ B _ in y ↦ let k : G y ≔ h y in G y
  > def annotated (h : (y :♭| A) → B y) : (y :♭| A) → Type ≔ let G : (_ :♭| A) → Type ≔ x ↦ _ in y ↦ let k : G y ≔ h y in G y
  > def keyed (h : (y :♭| A) → C y) : (y :♭| A) → Type ≔ let G : (_ :♭| A) → Type ≔ x ↦ _ in y ↦ let k : G y ≔ h y in G y
  > echo locked b0 a0
  > echo annotated b0 a0
  > echo keyed c0 a0
  > axiom d1 : D ((z : A) → C z)
  > def ambient : Type ≔ let k : D ((z : A) → let only x : A ≔ z in (_ : Type)) ≔ d1 in A
  > axiom t : (y :♭| A) → D Type
  > def mismatch : (y :♭| A) → Type ≔ y ↦ let k : D (let only x : A ≔ y in (_ : Type)) ≔ t y in A
  > EOF
  B a0
    : Type
  
  B a0
    : Type
  
  C a0
    : Type
  

An environment entry with a nonidentity key isn't a renaming.  A value can't use a variable with a different annotation than the one it renames.  And when the current context has locks that the metavariable's context doesn't, the value can't use variables behind them.

  $ narya -spatial - <<EOF
  > axiom A : Type
  > axiom C : A → Type
  > axiom D : (_ :♭| Type) → Type
  > def keyenv (h : (y :♭| A) → C y) : (y :♭| A) → Type ≔ let G : A → Type ≔ x ↦ C _ in y ↦ let k : G y ≔ h y in A
  > axiom e : (y :♭| A) → D (C y)
  > def mismatch2 : (y :♭| A) → Type ≔ y ↦ let k : D (let only x : A ≔ y in C (_ : A)) ≔ e y in A
  > axiom d2 : (y :♭| A) → D ((z : A) → C y)
  > def lockscope : (y :♭| A) → Type ≔ y ↦ let k : D ((z : A) → let only x : A ≔ z in (_ : Type)) ≔ d2 y in A
  > EOF
   ￫ error[E0401]
   ￭ stdin
   4 | def keyenv (h : (y :♭| A) → C y) : (y :♭| A) → Type ≔ let G : A → Type ≔ x ↦ C _ in y ↦ let k : G y ≔ h y in A
     ^ term synthesized type
         C y
       but is being checked against type
         C (let only … in ?u0)
       unequal head terms:
         y
       does not equal
         let only … in ?u0
  
   ￫ error[E0401]
   ￭ stdin
   6 | def mismatch2 : (y :♭| A) → Type ≔ y ↦ let k : D (let only x : A ≔ y in C (_ : A)) ≔ e y in A
     ^ term synthesized type
         D (C y)
       but is being checked against type
         D (C (let only … in ?u1))
       unequal head terms:
         y
       does not equal
         let only … in ?u1
  
   ￫ error[E0401]
   ￭ stdin
   8 | def lockscope : (y :♭| A) → Type ≔ y ↦ let k : D ((z : A) → let only x : A ≔ z in (_ : Type)) ≔ d2 y in A
     ^ term synthesized type
         D ((z : A) → C y)
       but is being checked against type
         D ((z : A) → let only … in ?u2)
       unequal head head terms:
         C
       does not equal
         let only … in ?u2
  
  [1]

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

A unification metavariable whose environment is not a renaming can't be solved yet.  This includes one used in a branch of a match against a variable, since the variable is substituted by a constructor there.  It is equal only to itself, and is displayed by number.

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
