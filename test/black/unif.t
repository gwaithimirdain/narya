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
   ￭ stdin
   3 | def x : A ≔ _
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   4 | def f (y : _) : A ≔ a
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   5 | def g (y : A) : A ≔ match y [ _ ↦ _ ]
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   6 | echo (_ : A)
     ^ can't determine a value for this placeholder
  
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
  
   ￫ error[E0406]
   ￭ stdin
   4 | def repeated (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ term synthesized type
         B a
       and is being checked against type
         B (let only … in ?u1)
       but can't determine whether they are equal, since comparing head terms
         a
       and
         let only … in ?u1
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   4 | def repeated (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   5 | def repeated2 : A → Type ≔ let G : A → A → Type ≔ p q ↦ B _ in y ↦ let k : Id Type (G y y) (B y) ≔ refl (B y) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B y) (B y)
       and is being checked against type
         Type⁽ᵉ⁾ (B (let only … in ?u3)) (B y)
       but can't determine whether they are equal, since comparing head terms
         y
       and
         let only … in ?u3
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   5 | def repeated2 : A → Type ≔ let G : A → A → Type ≔ p q ↦ B _ in y ↦ let k : Id Type (G y y) (B y) ≔ refl (B y) in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   8 | def repeated3 : A → Type ≔ let G : A → A → Type ≔ p q ↦ K _ _ in y ↦ let k : G y y ≔ kk _ in A
     ^ term synthesized type
         K (let only … in ?u5) (let only … in ?u5)
       and is being checked against type
         K (let only … in ?u5) (let only … in ?u6)
       but can't determine whether they are equal, since comparing head metavariables
         ?u5
       and
         ?u6
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   8 | def repeated3 : A → Type ≔ let G : A → A → Type ≔ p q ↦ K _ _ in y ↦ let k : G y y ≔ kk _ in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   8 | def repeated3 : A → Type ≔ let G : A → A → Type ≔ p q ↦ K _ _ in y ↦ let k : G y y ≔ kk _ in A
     ^ can't determine a value for this placeholder
  
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
   ￫ error[E0406]
   ￭ stdin
   1 | def tydep : (Z : Type) → Type ≔ let m : (X Y : Type) → X → Y → Y ≔ X Y ↦ _ in Z ↦ let k : Id (Z → Z → Z) (m Z Z) ((x y ↦ y) : Z → Z → Z) ≔ refl ((x y ↦ y) : Z → Z → Z) in Z
     ^ term synthesized type
         {𝑥₀ : Z} {𝑥₁ : Z} (𝑥₂ : Id Z 𝑥₀ 𝑥₁) {𝑦₀ : Z} {𝑦₁ : Z} (𝑦₂ : Id Z 𝑦₀ 𝑦₁)
         →⁽ᵉ⁾ Id Z 𝑦₀ 𝑦₁
       and is being checked against type
         {𝑥₀ : Z} {𝑥₁ : Z} (𝑥₂ : Id Z 𝑥₀ 𝑥₁) {𝑦₀ : Z} {𝑦₁ : Z} (𝑦₂ : Id Z 𝑦₀ 𝑦₁)
         →⁽ᵉ⁾ Id Z ((let only … in ?u0) 𝑥₀ 𝑦₀) 𝑦₁
       but can't determine whether they are equal, since comparing head terms
         𝑦
       and
         let only … in ?u0
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   1 | def tydep : (Z : Type) → Type ≔ let m : (X Y : Type) → X → Y → Y ≔ X Y ↦ _ in Z ↦ let k : Id (Z → Z → Z) (m Z Z) ((x y ↦ y) : Z → Z → Z) ≔ refl ((x y ↦ y) : Z → Z → Z) in Z
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   2 | def vardep : (Z : Type) (z : Z) (e : Z → Type) → Type ≔ let G : (X Y : Type) (c : X) (e : Y → Type) → Type ≔ X Y c e ↦ _ in Z z e ↦ let k : Id Type (G Z Z z e) (e z) ≔ refl (e z) in Type
     ^ term synthesized type
         Type⁽ᵉ⁾ (e z) (e z)
       and is being checked against type
         Type⁽ᵉ⁾ (let only … in ?u2) (e z)
       but can't determine whether they are equal, since comparing head terms
         e
       and
         let only … in ?u2
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   2 | def vardep : (Z : Type) (z : Z) (e : Z → Type) → Type ≔ let G : (X Y : Type) (c : X) (e : Y → Type) → Type ≔ X Y c e ↦ _ in Z z e ↦ let k : Id Type (G Z Z z e) (e z) ≔ refl (e z) in Type
     ^ can't determine a value for this placeholder
  
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
   ￫ error[E0406]
   ￭ stdin
   4 | def keyenv (h : (y :♭| A) → C y) : (y :♭| A) → Type ≔ let G : A → Type ≔ x ↦ C _ in y ↦ let k : G y ≔ h y in A
     ^ term synthesized type
         C y
       and is being checked against type
         C (let only … in ?u0)
       but can't determine whether they are equal, since comparing head terms
         y
       and
         let only … in ?u0
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   4 | def keyenv (h : (y :♭| A) → C y) : (y :♭| A) → Type ≔ let G : A → Type ≔ x ↦ C _ in y ↦ let k : G y ≔ h y in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   6 | def mismatch2 : (y :♭| A) → Type ≔ y ↦ let k : D (let only x : A ≔ y in C (_ : A)) ≔ e y in A
     ^ term synthesized type
         D (C y)
       and is being checked against type
         D (C (let only … in ?u2))
       but can't determine whether they are equal, since comparing head terms
         y
       and
         let only … in ?u2
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   6 | def mismatch2 : (y :♭| A) → Type ≔ y ↦ let k : D (let only x : A ≔ y in C (_ : A)) ≔ e y in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   8 | def lockscope : (y :♭| A) → Type ≔ y ↦ let k : D ((z : A) → let only x : A ≔ z in (_ : Type)) ≔ d2 y in A
     ^ term synthesized type
         D ((z : A) → C y)
       and is being checked against type
         D ((z : A) → let only … in ?u4)
       but can't determine whether they are equal, since comparing head head terms
         C
       and
         let only … in ?u4
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   8 | def lockscope : (y :♭| A) → Type ≔ y ↦ let k : D ((z : A) → let only x : A ≔ z in (_ : Type)) ≔ d2 y in A
     ^ can't determine a value for this placeholder
  
  [1]

A metavariable can be solved when it is applied to arguments, as long as they are plain variables, by abstracting over them.  This includes partial applications, cubes of arguments, and arguments of modal function-types.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom C : A → A → Type
  > axiom a0 : A
  > axiom a1 : A
  > axiom a2 : Id A a0 a1
  > def one : A → Type ≔ let f : A → Type ≔ _ in let k : (x : A) → Id Type (f x) (B x) ≔ x ↦ refl (B x) in f
  > about one
  > echo one a0
  > def two : A → A → Type ≔ let f : A → A → Type ≔ _ in let k : (y z : A) → Id Type (f y z) (C z y) ≔ y z ↦ refl (C z y) in f
  > echo two a0 a1
  > def part : A → A → Type ≔ let f : A → A → Type ≔ _ in let k : (y : A) → Id (A → Type) (f y) (C y) ≔ y ↦ refl (C y) in f
  > echo part a0 a1
  > def constfn (b : A) : A → Type ≔ let f : A → Type ≔ _ in let k : (x : A) → Id Type (f x) (B b) ≔ x ↦ refl (B b) in f
  > echo constfn a0 a1
  > axiom f0 : A → Type
  > axiom Q0 : (y0 y1 : A) (y2 : Id A y0 y1) → Id Type (f0 y0) (f0 y1)
  > def cub : Id (A → Type) f0 f0 ≔ let G : Id (A → Type) f0 f0 ≔ _ in let k : (y0 y1 : A) (y2 : Id A y0 y1) → Id (Id Type (f0 y0) (f0 y1)) (G y2) (Q0 y0 y1 y2) ≔ y0 y1 y2 ↦ refl (Q0 y0 y1 y2) in G
  > echo cub a2
  > EOF
  let f ≔ B in let k ≔ x ↦ Id (B x) in f
    : A → Type
  
  B a0
    : Type
  
  C a1 a0
    : Type
  
  C a0 a1
    : Type
  
  B a0
    : Type
  
  Q0 a0 a1 a2
    : Type⁽ᵉ⁾ (f0 a0) (f0 a1)
  

  $ narya -spatial - <<EOF
  > axiom A : Type
  > axiom B : (_ :♭| A) → Type
  > axiom a0 : A
  > def modal : (_ :♭| A) → Type ≔ let f : (_ :♭| A) → Type ≔ _ in let k : (y :♭| A) → Id Type (f y) (B y) ≔ y ↦ refl (B y) in f
  > echo modal a0
  > EOF
  B a0
    : Type
  

Solutions are eta-contracted when possible, omitting final arguments that agree on both sides, including when the other side is also a metavariable.  This only happens when the omitted argument doesn't also occur elsewhere.  Otherwise, the bound variables are named according to the type of the metavariable.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom C : A → A → Type
  > axiom a0 : A
  > axiom a1 : A
  > def eta1 : A → Type ≔ let f : (w : A) → Type ≔ _ in let k : (x : A) → Id Type (f x) (B x) ≔ x ↦ refl (B x) in f
  > about eta1
  > def eta2 : A → A → Type ≔ let f : (u v : A) → Type ≔ _ in let k : (y z : A) → Id Type (f y z) (C y z) ≔ y z ↦ refl (C y z) in f
  > about eta2
  > def swapped : A → A → Type ≔ let f : (u v : A) → Type ≔ _ in let k : (y z : A) → Id Type (f y z) (C z y) ≔ y z ↦ refl (C z y) in f
  > about swapped
  > echo swapped a0 a1
  > def partial (D : A → A → A → Type) : A → A → Type ≔ let f : (u v : A) → Type ≔ _ in let k : (y z : A) → Id Type (f y z) (D y y z) ≔ y z ↦ refl (D y y z) in f
  > about partial
  > echo partial (x y z ↦ C x z) a0 a1
  > def nocontract : A → Type ≔ let f : (w : A) → Type ≔ _ in let k : (x : A) → Id Type (f x) (C x x) ≔ x ↦ refl (C x x) in f
  > about nocontract
  > def flexflex : A → Type ≔ let f : (w : A) → Type ≔ _ in let g : (w : A) → Type ≔ _ in let k : (x : A) → Id Type (f x) (g x) ≔ x ↦ refl (g x) in let j : (x : A) → Id Type (g x) (B x) ≔ x ↦ refl (B x) in f
  > about flexflex
  > echo flexflex a0
  > EOF
  let f ≔ B in let k ≔ x ↦ Id (B x) in f
    : A → Type
  
  let f ≔ C in let k ≔ y z ↦ Id (C y z) in f
    : A → A → Type
  
  let f ≔ u v ↦ C v u in let k ≔ y z ↦ Id (C z y) in f
    : A → A → Type
  
  C a1 a0
    : Type
  
  D ↦ let f ≔ u ↦ D u u in let k ≔ y z ↦ Id (D y y z) in f
    : (D : A → A → A → Type) → A → A → Type
  
  C a0 a1
    : Type
  
  let f ≔ w ↦ C w w in let k ≔ x ↦ Id (C x x) in f
    : A → Type
  
  let f ≔ B in let g ≔ f in let k ≔ x ↦ Id (g x) in let j ≔ x ↦ Id (B x) in f
    : A → Type
  
  B a0
    : Type
  

After contracting to a metavariable, its later solution can still use its argument.  But we can't contract if that metavariable's environment contains the omitted variable, and then the variable flows through that environment.  A metavariable also can't be solved by one created inside its own let-binding, since the environment of the latter contains the former.

  $ narya - <<EOF
  > axiom A : Type
  > axiom C : A → A → Type
  > axiom a0 : A
  > axiom a1 : A
  > def later : A → Type ≔ let f : (w : A) → Type ≔ _ in let g : (w : A) → Type ≔ _ in let k : (x : A) → Id Type (f x) (g x) ≔ x ↦ refl (g x) in let j : (x : A) → Id Type (g x) (C x x) ≔ x ↦ refl (C x x) in f
  > about later
  > echo later a0
  > def inenv : A → A → Type ≔ let f : (w : A) → Type ≔ _ in x ↦ let g : (w : A) → Type ≔ let only x' : A ≔ x in (_ : A → Type) in let k : Id Type (f x) (g x) ≔ refl (g x) in let j : (z : A) → Id Type (g z) (C x z) ≔ z ↦ refl (C x z) in f
  > about inenv
  > echo inenv a0 a1
  > def scoped : A → Type ≔ let f : (w : A) → Type ≔ _ in x ↦ let g : (w : A) → Type ≔ _ in let k : Id Type (f x) (g x) ≔ refl (g x) in A
  > EOF
  let f ≔ w ↦ C w w in
  let g ≔ f in
  let k ≔ x ↦ Id (g x) in
  let j ≔ x ↦ Id (C x x) in
  f
    : A → Type
  
  C a0 a0
    : Type
  
  let f ≔ w ↦ C w w in
  x ↦
  let g ≔ let only x' : A ≔ x in C x' in
  let k ≔ Id (g x) in
  let j ≔ z ↦ Id (C x z) in
  f
    : A → A → Type
  
  C a1 a1
    : Type
  
   ￫ error[E0406]
   ￭ stdin
   11 | def scoped : A → Type ≔ let f : (w : A) → Type ≔ _ in x ↦ let g : (w : A) → Type ≔ _ in let k : Id Type (f x) (g x) ≔ refl (g x) in A
      ^ term synthesized type
          Type⁽ᵉ⁾ (g x) (g x)
        and is being checked against type
          Type⁽ᵉ⁾ (f x) (g x)
        but can't determine whether they are equal, since comparing head metavariables
          ?u5
        and
          ?u4
        depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   11 | def scoped : A → Type ≔ let f : (w : A) → Type ≔ _ in x ↦ let g : (w : A) → Type ≔ _ in let k : Id Type (f x) (g x) ≔ refl (g x) in A
      ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   11 | def scoped : A → Type ≔ let f : (w : A) → Type ≔ _ in x ↦ let g : (w : A) → Type ≔ _ in let k : Id Type (f x) (g x) ≔ refl (g x) in A
      ^ can't determine a value for this placeholder
  
  [1]

Eta-contraction doesn't change the problem: ?f x x =? h x uses a repeated variable, even though ?f x =? h wouldn't.

  $ narya - <<EOF
  > axiom A : Type
  > axiom h : A → Type
  > def repeated : Type ≔ let f : A → A → Type ≔ _ in let k : (x : A) → Id Type (f x x) (h x) ≔ x ↦ refl (h x) in A
  > EOF
   ￫ error[E0406]
   ￭ stdin
   3 | def repeated : Type ≔ let f : A → A → Type ≔ _ in let k : (x : A) → Id Type (f x x) (h x) ≔ x ↦ refl (h x) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (h x) (h x)
       and is being checked against type
         Type⁽ᵉ⁾ (f x x) (h x)
       but can't determine whether they are equal, since comparing head terms
         h
       and
         f
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   3 | def repeated : Type ≔ let f : A → A → Type ≔ _ in let k : (x : A) → Id Type (f x x) (h x) ≔ x ↦ refl (h x) in A
     ^ can't determine a value for this placeholder
  
  [1]

The arguments count as part of the renaming, so the value can't use an argument that is repeated or also appears in the environment, since then there would be more than one solution.  An argument that isn't a variable isn't a renaming, the value can't use other variables, and the metavariable can't occur in it.  Well-typedness is also checked as before.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom a0 : A
  > def envarg : A → Type ≔ x ↦ let f : A → Type ≔ _ in let k : Id Type (f x) (B x) ≔ refl (B x) in A
  > def reparg : Type ≔ let f : A → A → Type ≔ _ in let k : (y : A) → Id Type (f y y) (B y) ≔ y ↦ refl (B y) in A
  > def nonvar : Type ≔ let f : A → Type ≔ _ in let k : Id Type (f a0) (B a0) ≔ refl (B a0) in A
  > def scope : Type ≔ let f : A → Type ≔ _ in let k : (x w : A) → Id Type (f x) (B w) ≔ x w ↦ refl (B w) in A
  > def occurs (F : Type → Type) : Type ≔ let f : A → Type ≔ _ in let k : (x : A) → Id Type (f x) (F (f x)) ≔ x ↦ refl (F (f x)) in A
  > def tydep : (Z : Type) → Type ≔ let m : (X Y : Type) → X → Y → Y ≔ _ in Z ↦ let k : Id (Z → Z → Z) (m Z Z) ((x y ↦ y) : Z → Z → Z) ≔ refl ((x y ↦ y) : Z → Z → Z) in Z
  > def vardep : (Z : Type) (z : Z) (e : Z → Type) → Type ≔ let G : (X Y : Type) (c : X) (e : Y → Type) → Type ≔ _ in Z z e ↦ let k : Id Type (G Z Z z e) (e z) ≔ refl (e z) in Type
  > EOF
   ￫ error[E0406]
   ￭ stdin
   4 | def envarg : A → Type ≔ x ↦ let f : A → Type ≔ _ in let k : Id Type (f x) (B x) ≔ refl (B x) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B x) (B x)
       and is being checked against type
         Type⁽ᵉ⁾ (f x) (B x)
       but can't determine whether they are equal, since comparing head terms
         B
       and
         f
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   4 | def envarg : A → Type ≔ x ↦ let f : A → Type ≔ _ in let k : Id Type (f x) (B x) ≔ refl (B x) in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   5 | def reparg : Type ≔ let f : A → A → Type ≔ _ in let k : (y : A) → Id Type (f y y) (B y) ≔ y ↦ refl (B y) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B y) (B y)
       and is being checked against type
         Type⁽ᵉ⁾ (f y y) (B y)
       but can't determine whether they are equal, since comparing head terms
         B
       and
         f
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   5 | def reparg : Type ≔ let f : A → A → Type ≔ _ in let k : (y : A) → Id Type (f y y) (B y) ≔ y ↦ refl (B y) in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   6 | def nonvar : Type ≔ let f : A → Type ≔ _ in let k : Id Type (f a0) (B a0) ≔ refl (B a0) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B a0) (B a0)
       and is being checked against type
         Type⁽ᵉ⁾ (f a0) (B a0)
       but can't determine whether they are equal, since comparing head terms
         B
       and
         f
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   6 | def nonvar : Type ≔ let f : A → Type ≔ _ in let k : Id Type (f a0) (B a0) ≔ refl (B a0) in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E0401]
   ￭ stdin
   7 | def scope : Type ≔ let f : A → Type ≔ _ in let k : (x w : A) → Id Type (f x) (B w) ≔ x w ↦ refl (B w) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B w) (B w)
       but is being checked against type
         Type⁽ᵉ⁾ (f x) (B w)
       unequal head terms:
         B
       does not equal
         f
  
   ￫ error[E0401]
   ￭ stdin
   8 | def occurs (F : Type → Type) : Type ≔ let f : A → Type ≔ _ in let k : (x : A) → Id Type (f x) (F (f x)) ≔ x ↦ refl (F (f x)) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (F (f x)) (F (f x))
       but is being checked against type
         Type⁽ᵉ⁾ (f x) (F (f x))
       unequal head terms:
         F
       does not equal
         f
  
   ￫ error[E0406]
   ￭ stdin
   9 | def tydep : (Z : Type) → Type ≔ let m : (X Y : Type) → X → Y → Y ≔ _ in Z ↦ let k : Id (Z → Z → Z) (m Z Z) ((x y ↦ y) : Z → Z → Z) ≔ refl ((x y ↦ y) : Z → Z → Z) in Z
     ^ term synthesized type
         {𝑥₀ : Z} {𝑥₁ : Z} (𝑥₂ : Id Z 𝑥₀ 𝑥₁) {𝑦₀ : Z} {𝑦₁ : Z} (𝑦₂ : Id Z 𝑦₀ 𝑦₁)
         →⁽ᵉ⁾ Id Z 𝑦₀ 𝑦₁
       and is being checked against type
         {𝑥₀ : Z} {𝑥₁ : Z} (𝑥₂ : Id Z 𝑥₀ 𝑥₁) {𝑦₀ : Z} {𝑦₁ : Z} (𝑦₂ : Id Z 𝑦₀ 𝑦₁)
         →⁽ᵉ⁾ Id Z (m Z Z 𝑥₀ 𝑦₀) 𝑦₁
       but can't determine whether they are equal, since comparing head terms
         𝑦
       and
         m
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   9 | def tydep : (Z : Type) → Type ≔ let m : (X Y : Type) → X → Y → Y ≔ _ in Z ↦ let k : Id (Z → Z → Z) (m Z Z) ((x y ↦ y) : Z → Z → Z) ≔ refl ((x y ↦ y) : Z → Z → Z) in Z
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   10 | def vardep : (Z : Type) (z : Z) (e : Z → Type) → Type ≔ let G : (X Y : Type) (c : X) (e : Y → Type) → Type ≔ _ in Z z e ↦ let k : Id Type (G Z Z z e) (e z) ≔ refl (e z) in Type
      ^ term synthesized type
          Type⁽ᵉ⁾ (e z) (e z)
        and is being checked against type
          Type⁽ᵉ⁾ (G Z Z z e) (e z)
        but can't determine whether they are equal, since comparing head terms
          e
        and
          G
        depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   10 | def vardep : (Z : Type) (z : Z) (e : Z → Type) → Type ≔ let G : (X Y : Type) (c : X) (e : Y → Type) → Type ≔ _ in Z z e ↦ let k : Id Type (G Z Z z e) (e z) ≔ refl (e z) in Type
      ^ can't determine a value for this placeholder
  
  [1]

A metavariable that is projected from is expanded into a tuple of new metavariables, when solving an equation that requires it, which is correct by eta-conversion.  This includes dependent and nested records, and metavariables that are also applied to arguments.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom a0 : A
  > axiom a1 : A
  > axiom b0 : B a0
  > def Pr : Type ≔ sig (fst : A, snd : A)
  > def Si : Type ≔ sig (fst : A, snd : B fst)
  > def both : Pr ≔ let p : Pr ≔ _ in let k : Id A (p .fst) a0 ≔ refl a0 in let j : Id A (p .snd) a1 ≔ refl a1 in p
  > about both
  > def dep : Si ≔ let p : Si ≔ _ in let k : Id A (p .fst) a0 ≔ refl a0 in let j : Id (B a0) (p .snd) b0 ≔ refl b0 in p
  > about dep
  > def fn : A → Pr ≔ let f : A → Pr ≔ _ in let k : (x : A) → Id A (f x .fst) x ≔ x ↦ refl x in let j : (x : A) → Id A (f x .snd) x ≔ x ↦ refl x in f
  > about fn
  > echo fn a0 .snd
  > def nested : A ≔ let q : sig (l : Pr, r : A) ≔ _ in let k : Id A (q .l .snd) a0 ≔ refl a0 in let j : Id A (q .l .fst) a1 ≔ refl a1 in let m : Id A (q .r) a0 ≔ refl a0 in q .l .fst
  > echo nested
  > def swap : Pr → Pr ≔ let f : Pr → Pr ≔ _ in let k : (z : Pr) → Id A (f z .fst) (z .snd) ≔ z ↦ refl (z .snd) in let j : (z : Pr) → Id A (f z .snd) (z .fst) ≔ z ↦ refl (z .fst) in f
  > about swap
  > EOF
  let p ≔ (fst ≔ a0, snd ≔ a1) in let k ≔ refl a0 in let j ≔ refl a1 in p
    : Pr
  
  let p ≔ (fst ≔ a0, snd ≔ b0) in let k ≔ refl a0 in let j ≔ refl b0 in p
    : Si
  
  let f ≔ 𝑥 ↦ (fst ≔ 𝑥, snd ≔ 𝑥) in
  let k ≔ x ↦ refl x in
  let j ≔ x ↦ refl x in
  f
    : A → Pr
  
  a0
    : A
  
  a1
    : A
  
  let f ≔ 𝑥 ↦ (fst ≔ 𝑥 .snd, snd ≔ 𝑥 .fst) in
  let k ≔ z ↦ refl (z .snd) in
  let j ≔ z ↦ refl (z .fst) in
  f
    : Pr → Pr
  

The other fields stay unknown, and can leave unsolved metavariables.  A codatatype without eta can't be expanded.  And for now, neither can a metavariable with different fields on both sides.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a0 : A
  > def Pr : Type ≔ sig (fst : A, snd : A)
  > def S : Type ≔ codata [ x .head : A | x .tail : S ]
  > def onefield : A ≔ let p : Pr ≔ _ in let k : Id A (p .fst) a0 ≔ refl a0 in a0
  > def stream : A ≔ let s : S ≔ _ in let k : Id A (s .head) a0 ≔ refl a0 in a0
  > def samem : A ≔ let p : Pr ≔ _ in let k : Id A (p .fst) (p .snd) ≔ refl (p .snd) in a0
  > EOF
   ￫ error[E2004]
   ￭ stdin
   5 | def onefield : A ≔ let p : Pr ≔ _ in let k : Id A (p .fst) a0 ≔ refl a0 in a0
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   6 | def stream : A ≔ let s : S ≔ _ in let k : Id A (s .head) a0 ≔ refl a0 in a0
     ^ term synthesized type
         Id A a0 a0
       and is being checked against type
         Id A (s .head) a0
       but can't determine whether they are equal, since comparing head terms
         a0
       and
         s
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   6 | def stream : A ≔ let s : S ≔ _ in let k : Id A (s .head) a0 ≔ refl a0 in a0
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   7 | def samem : A ≔ let p : Pr ≔ _ in let k : Id A (p .fst) (p .snd) ≔ refl (p .snd) in a0
     ^ term synthesized type
         Id A (p .snd) (p .snd)
       and is being checked against type
         Id A (p .fst) (p .snd)
       but can't determine whether they are equal, since comparing fields
         snd
       and
         fst
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   7 | def samem : A ≔ let p : Pr ≔ _ in let k : Id A (p .fst) (p .snd) ≔ refl (p .snd) in a0
     ^ can't determine a value for this placeholder
  
  [1]

The component of a modal field lives behind a lock, and possibly at a different mode, and so does the metavariable created for it.  Its environment involves the counit of the adjunction, so for now it can only be solved by a value that doesn't use the variables behind that lock.

  $ narya -adjunction - <<EOF
  > axiom C : Type
  > axiom c : C
  > axiom c2 : C
  > def □′ (A :□| Type) : Disc ≔ sig ( (x :△| _) .□ : A )
  > def closed : C ≔ let r :△| □′ C ≔ _ in let k : Id C ((r :△| _) .□) c ≔ refl c in (r :△| _) .□
  > echo closed
  > about closed
  > def param (z :△□| C) : C ≔ let r :△| □′ C ≔ _ in let k : Id C ((r :△| _) .□) c ≔ refl c in (r :△| _) .□
  > echo param c2
  > def twofields : C ≔ let r :△| sig ( (x :△| _) .a : C, (x :△| _) .b : C ) ≔ _ in let k : Id C ((r :△| _) .a) c ≔ refl c in let j : Id C ((r :△| _) .b) c2 ≔ refl c2 in (r :△| _) .b
  > echo twofields
  > def varrhs (z :△□| C) : C ≔ let r :△| □′ C ≔ _ in let k : Id C ((r :△| _) .□) z ≔ refl z in (r :△| _) .□
  > EOF
  c
    : C
  
  let r :△| _ ≔ (□ ≔ c) in let k ≔ refl c in (r :△| _) .□
    : C
  
  c
    : C
  
  c2
    : C
  
   ￫ error[E0406]
   ￭ stdin
   12 | def varrhs (z :△□| C) : C ≔ let r :△| □′ C ≔ _ in let k : Id C ((r :△| _) .□) z ≔ refl z in (r :△| _) .□
      ^ term synthesized type
          Id C z z
        and is being checked against type
          Id C ?u8 z
        but can't determine whether they are equal, since comparing head terms
          z
        and
          ?u8
        depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   12 | def varrhs (z :△□| C) : C ≔ let r :△| □′ C ≔ _ in let k : Id C ((r :△| _) .□) z ≔ refl z in (r :△| _) .□
      ^ can't determine a value for this placeholder
  
  [1]

  $ narya -spatial - <<EOF
  > def N : Type ≔ data [ zero. | suc. (_ : N) ]
  > def R : Type ≔ sig ( (x :♭| _) .fst : N )
  > def samemode : N ≔ let r :♭| R ≔ _ in let k : Id N ((r :♭| _) .fst) zero. ≔ refl (zero. : N) in (r :♭| _) .fst
  > echo samemode
  > EOF
  0
    : N
  

A comparison of two neutral spines can fail and then succeed by unfolding them, so it can't solve anything unless the spines are forced to be equal.  Here g ignores its arguments, so the first is not constrained, and the second can be solved by a later constraint.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a1 : A
  > axiom a2 : A
  > axiom b1 : A
  > axiom b2 : A
  > axiom c : A
  > def g (x y : A) : A ≔ c
  > def unconstrained : A ≔ let v : A ≔ _ in let k : Id A (g v b1) (g a1 b2) ≔ refl (g a1 b2) in v
  > def later : A ≔ let v : A ≔ _ in let k : Id A (g v b1) (g a1 b2) ≔ refl (g a1 b2) in let j : Id A v a2 ≔ refl a2 in v
  > echo later
  > EOF
   ￫ error[E2004]
   ￭ stdin
   8 | def unconstrained : A ≔ let v : A ≔ _ in let k : Id A (g v b1) (g a1 b2) ≔ refl (g a1 b2) in v
     ^ can't determine a value for this placeholder
  
  a2
    : A
  
  [1]

Spines are forced to be equal if the head is a variable or an axiom, or a canonical type (including function-types and instantiated identity types), or a case tree stuck on something other than a metavariable.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a1 : A
  > axiom F : Type → Type
  > def Pr (X Y : Type) : Type ≔ sig (fst : X, snd : Y)
  > def Vec (X : Type) : Type ≔ data [ nil. | cons. (_ : X) (_ : Vec X) ]
  > def inj1 : Type ≔ let X : Type ≔ _ in let k : Id Type (F X) (F A) ≔ refl (F A) in X
  > echo inj1
  > def inj2 : Type ≔ let X : Type ≔ _ in let k : Id Type (Vec X) (Vec A) ≔ refl (Vec A) in X
  > echo inj2
  > def inj3 : Type ≔ let X : Type ≔ _ in let k : Id Type (Pr X A) (Pr A A) ≔ refl (Pr A A) in X
  > echo inj3
  > def inj4 : Type ≔ let X : Type ≔ _ in let k : Id Type (X → A) (A → A) ≔ refl (A → A) in X
  > echo inj4
  > def inj5 : Type ≔ let X : Type ≔ _ in let k : Id Type (A → X) (A → A) ≔ refl (A → A) in X
  > echo inj5
  > def inj6 (e : A → A) : A ≔ let x : A ≔ _ in let k : Id A (e x) (e a1) ≔ refl (e a1) in x
  > echo inj6 (x ↦ x)
  > def inj7 : A ≔ let x : A ≔ _ in let k : Id Type (Id A x a1) (Id A a1 a1) ≔ refl (Id A a1 a1) in x
  > echo inj7
  > def Bool : Type ≔ data [ t. | f. ]
  > def st (b : Bool) (y : A) : A ≔ match b [ t. ↦ y | f. ↦ y ]
  > def inj8 (b : Bool) : A ≔ let x : A ≔ _ in let k : Id A (st b x) (st b a1) ≔ refl (st b a1) in x
  > echo inj8 t.
  > EOF
  A
    : Type
  
  A
    : Type
  
  A
    : Type
  
  A
    : Type
  
  A
    : Type
  
  a1
    : A
  
  a1
    : A
  
  a1
    : A
  

But they aren't forced if it is stuck on a metavariable, or if the head is a metavariable, since a solution of that metavariable could ignore them.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a1 : A
  > def Bool : Type ≔ data [ t. | f. ]
  > def st (b : Bool) (y : A) : A ≔ match b [ t. ↦ y | f. ↦ y ]
  > def stuck : A ≔ let c : Bool ≔ _ in let x : A ≔ _ in let k : Id A (st c x) (st c a1) ≔ refl (st c a1) in a1
  > def head : A ≔ let m : A → A ≔ _ in let x : A ≔ _ in let k : Id A (m x) (m a1) ≔ refl (m a1) in a1
  > EOF
   ￫ error[E0406]
   ￭ stdin
   5 | def stuck : A ≔ let c : Bool ≔ _ in let x : A ≔ _ in let k : Id A (st c x) (st c a1) ≔ refl (st c a1) in a1
     ^ term synthesized type
         Id A (st c a1) (st c a1)
       and is being checked against type
         Id A (st c x) (st c a1)
       but can't determine whether they are equal, since comparing head terms
         a1
       and
         x
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   5 | def stuck : A ≔ let c : Bool ≔ _ in let x : A ≔ _ in let k : Id A (st c x) (st c a1) ≔ refl (st c a1) in a1
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   5 | def stuck : A ≔ let c : Bool ≔ _ in let x : A ≔ _ in let k : Id A (st c x) (st c a1) ≔ refl (st c a1) in a1
     ^ can't determine a value for this placeholder
  
   ￫ error[E0406]
   ￭ stdin
   6 | def head : A ≔ let m : A → A ≔ _ in let x : A ≔ _ in let k : Id A (m x) (m a1) ≔ refl (m a1) in a1
     ^ term synthesized type
         Id A (m a1) (m a1)
       and is being checked against type
         Id A (m x) (m a1)
       but can't determine whether they are equal, since comparing head terms
         a1
       and
         x
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   6 | def head : A ≔ let m : A → A ≔ _ in let x : A ≔ _ in let k : Id A (m x) (m a1) ≔ refl (m a1) in a1
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   6 | def head : A ≔ let m : A → A ≔ _ in let x : A ≔ _ in let k : Id A (m x) (m a1) ≔ refl (m a1) in a1
     ^ can't determine a value for this placeholder
  
  [1]

At the end of a command, a metavariable with a singleton type, up to eta-conversion, is solved even if nothing has constrained it.  This includes records with all fields singletons, functions with singleton codomains, and the other fields of an expanded metavariable.  It also happens soon enough for echo to know that it can print.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a0 : A
  > def Top : Type ≔ sig ()
  > def u : Top ≔ _
  > about u
  > def fn : (x : A) → Top ≔ _
  > about fn
  > def nest : sig (a : Top, b : A → Top) ≔ _
  > about nest
  > echo (_ : Top)
  > def Dep : Top → Type ≔ x ↦ Top
  > def dep : sig (x : Top, y : Dep x) ≔ _
  > about dep
  > def Pr : Type ≔ sig (fst : A, snd : Top)
  > def part : Pr ≔ let p : Pr ≔ _ in let k : Id A (p .fst) a0 ≔ refl a0 in p
  > about part
  > def hi (a b : A) (p : Id A a b) : Id Top _ _ ≔ _
  > EOF
  ()
    : Top
  
  x ↦ ()
    : (x : A) → Top
  
  (a ≔ (), b ≔ 𝑥 ↦ ())
    : sig #(gen) (
        a : Top,
        b : A → Top )
  
  ()
    : Top
  
  (x ≔ (), y ≔ ())
    : sig #(gen) (
        x : Top,
        y : Dep x )
  
  let p ≔ (fst ≔ a0, snd ≔ ()) in let k ≔ refl a0 in p
    : Pr
  

  $ narya -adjunction - <<EOF
  > def Top : Type ≔ sig ()
  > def □′ (A :□| Type) : Disc ≔ sig ( (x :△| _) .□ : A )
  > def modal : □′ Top ≔ _
  > about modal
  > EOF
  (□ ≔ ())
    : □′ Top
  

A modal field that disappears at some dimension isn't part of a tuple at that dimension, so it isn't part of an expansion either.

  $ narya -parametric -discrete-spatial - <<EOF
  > axiom A : Type
  > def Top : Type ≔ sig ()
  > def R : Type ≔ sig ((x :♭| _) .f : A, x .g : Top)
  > axiom r : R
  > def hd : Id R r r ≔ let v : Id R r r ≔ _ in let k : Id (Id Top (r .g) (r .g)) (v .g) (refl (r .g)) ≔ refl (refl (r .g)) in v
  > echo hd
  > def sing : Id R r r ≔ _
  > echo sing
  > EOF
  (g ≔ ())
    : R⁽ᵉ⁾ r r
  
  (g ≔ ())
    : R⁽ᵉ⁾ r r
  

An instantiation of a higher-dimensional Gel is a record, so it can be a singleton.  A symmetry of one isn't a record, although it inherits an eta-rule from one, so it is also a singleton, as shown by the explicit element below.  A metavariable of such a type is solved by a symmetry of a tuple.

  $ narya -parametric - <<EOF
  > def Top : Type ≔ sig ()
  > def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig ( a .ungel : R a.0 a.1 )
  > axiom A : Type
  > axiom B : Type
  > def R : A → B → Type ≔ x y ↦ Top
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom b₀ : B
  > axiom b₁ : B
  > axiom b₂ : Id B b₀ b₁
  > def plain : refl (Gel A B R) a₂ b₂ (ungel ≔ ()) (ungel ≔ ()) ≔ _
  > echo plain
  > def bysym : (Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} ((),) {a₁} {b₁} ((),) a₂ b₂ ≔ sym (ungel ≔ ())
  > echo bysym
  > def symmed : (Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} ((),) {a₁} {b₁} ((),) a₂ b₂ ≔ _
  > echo symmed
  > def symplace : (Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} ((),) {a₁} {b₁} ((),) a₂ b₂ ≔ sym _
  > echo symplace
  > EOF
  (ungel ≔ ())
    : Gel⁽ᵉ⁾ (Id A) (Id B) (Id R) a₂ b₂ (ungel ≔ ()) (ungel ≔ ())
  
  sym (ungel ≔ ())
    : sym (Gel⁽ᵉ⁾ (Id A) (Id B) (Id R)) {a₀} {b₀} (_ ≔ ()) {a₁} {b₁} (_ ≔ ())
        a₂ b₂
  
  sym (ungel ≔ ())
    : sym (Gel⁽ᵉ⁾ (Id A) (Id B) (Id R)) {a₀} {b₀} (_ ≔ ()) {a₁} {b₁} (_ ≔ ())
        a₂ b₂
  
  sym (ungel ≔ ())
    : sym (Gel⁽ᵉ⁾ (Id A) (Id B) (Id R)) {a₀} {b₀} (_ ≔ ()) {a₁} {b₁} (_ ≔ ())
        a₂ b₂
  

The permutation may not be its own inverse, and the type can have boundaries that are symmetrized too.  Here we get the type from the first argument of a function.

  $ narya -parametric - <<EOF
  > def Top : Type ≔ sig ()
  > def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig ( a .ungel : R a.0 a.1 )
  > def R : Top → Top → Type ≔ x y ↦ Top
  > def g : Gel Top Top R () () ≔ (ungel ≔ ())
  > def two (X : Type) (x y : X) : X ≔ y
  > echo two _ (refl (refl g)) _
  > echo two _ ((refl (refl g))⁽²³¹⁾) _
  > echo two _ ((refl (refl g))⁽³¹²⁾) _
  > EOF
  (ungel ≔ ())
    : Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾ {()} {()} {()} {()} {()} {()} {()} {()}
        () {()} {()} {()} {()} {()} {()} {()} {()} () (refl g) (refl g)
        (refl g) (refl g)
  
  (ungel ≔ ())⁽²³¹⁾
    : (Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²³¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ () ()
  
  (ungel ≔ ())⁽²¹³⁾
    : (Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²¹³⁾ (refl g) (refl g) {()} {()} ()
        {()} {()} () g⁽ᵉ¹⁾ g⁽ᵉ¹⁾
  

Other types aren't singletons, even if they have one constructor, and neither is a type that is an unsolved metavariable.

  $ narya - <<EOF
  > axiom A : Type
  > def Top : Type ≔ sig ()
  > def Pr : Type ≔ sig (fst : A, snd : Top)
  > def One : Type ≔ data [ one. ]
  > def notsing : Pr ≔ _
  > def data1 : One ≔ _
  > def neutralty (T : Type) : T ≔ _
  > def metaty : Top ≔ let X : Type ≔ _ in let y : X ≔ _ in ()
  > EOF
   ￫ error[E2004]
   ￭ stdin
   5 | def notsing : Pr ≔ _
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   6 | def data1 : One ≔ _
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   7 | def neutralty (T : Type) : T ≔ _
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   8 | def metaty : Top ≔ let X : Type ≔ _ in let y : X ≔ _ in ()
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   8 | def metaty : Top ≔ let X : Type ≔ _ in let y : X ≔ _ in ()
     ^ can't determine a value for this placeholder
  
  [1]

A metavariable with a permutation on it can be solved by inverting the permutation.

  $ narya -parametric - <<EOF
  > axiom A : Type
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > axiom a₂₀ : Id A a₀₀ a₁₀
  > axiom a₂₁ : Id A a₀₁ a₁₁
  > axiom t : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > echo rf _ t : Same _ t (sym _)
  > echo rf _ (sym t) : Same _ (sym t) (sym _)
  > echo rf _ t : Same _ t (sym (sym _))
  > axiom f : A → Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > axiom use : (F : A → Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁)
  >   → ((x : A) → Same (Id (Id A) a₂₀ a₂₁ a₀₂ a₁₂) (sym (F x)) (sym (f x))) → Type
  > echo use _ (x ↦ rf _ (sym (f x)))
  > axiom use2 : (F : A → Id (Id A) a₂₀ a₂₁ a₀₂ a₁₂)
  >   → ((x : A) → Same (Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁) (f x) (sym (F x))) → Type
  > echo use2 _ (x ↦ rf _ (f x))
  > EOF
  rf (A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁) t
    : Same (A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁) t t
  
  rf (A⁽ᵉᵉ⁾ a₂₀ a₂₁ a₀₂ a₁₂) (sym t)
    : Same (A⁽ᵉᵉ⁾ a₂₀ a₂₁ a₀₂ a₁₂) (sym t) (sym t)
  
  rf (A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁) t
    : Same (A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁) t t
  
  use f (x ↦ rf (A⁽ᵉᵉ⁾ a₂₀ a₂₁ a₀₂ a₁₂) (sym (f x)))
    : Type
  
  use2 (𝑥 ↦ sym (f 𝑥)) (x ↦ rf (A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁) (f x))
    : Type
  

This includes permutations that aren't their own inverse, and one can be solved with a value having a different permutation.  We use a record type here since its higher-dimensional instances are not symmetric in the Gel direction.

  $ narya -parametric - <<EOF
  > def Top : Type ≔ sig ()
  > axiom C : Type
  > axiom c : C
  > def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig ( a .ungel : R a.0 a.1 )
  > def R : Top → Top → Type ≔ x y ↦ C
  > def g : Gel Top Top R () () ≔ (ungel ≔ c)
  > def g3 ≔ refl (refl g)
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > echo rf _ (g3⁽²³¹⁾) : Same _ (g3⁽²³¹⁾) (_⁽²³¹⁾)
  > echo rf _ (g3⁽³¹²⁾) : Same _ (g3⁽³¹²⁾) (_⁽³¹²⁾)
  > echo rf _ (g3⁽²³¹⁾) : Same _ (g3⁽²³¹⁾) (_⁽³¹²⁾)
  > EOF
  rf ((Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²³¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ () ())
    g⁽ᵉᵉ¹⁾
    : Same
        ((Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²³¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ () ())
        g⁽ᵉᵉ¹⁾ g⁽ᵉᵉ¹⁾
  
  rf
    ((Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²¹³⁾ (refl g) (refl g) {()} {()} () {()}
       {()} () g⁽ᵉ¹⁾ g⁽ᵉ¹⁾) g⁽ᵉ¹ᵉ⁾
    : Same
        ((Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²¹³⁾ (refl g) (refl g) {()} {()} ()
           {()} {()} () g⁽ᵉ¹⁾ g⁽ᵉ¹⁾) g⁽ᵉ¹ᵉ⁾ g⁽ᵉ¹ᵉ⁾
  
  rf ((Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²³¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ () ())
    g⁽ᵉᵉ¹⁾
    : Same
        ((Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²³¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ () ())
        g⁽ᵉᵉ¹⁾ g⁽ᵉᵉ¹⁾
  

A metavariable with a permutation isn't equal to itself without it, even if the two have the same type.  This applies to holes too.

  $ narya -parametric - <<EOF
  > axiom A : Type
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > axiom a₂₀ : Id A a₀₀ a₁₀
  > axiom a₂₁ : Id A a₀₁ a₁₁
  > axiom t : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > axiom a : A
  > def T : Type ≔ Id (Id A) (refl a) (refl a) (refl a) (refl a)
  > axiom use : (m : T) → Same T m (sym m) → Type
  > echo use _ (rf T _)
  > def eqn : Type ≔ let m : T ≔ ? in use m (rf T m)
  > EOF
   ￫ error[E0406]
   ￭ stdin
   16 | echo use _ (rf T _)
      ^ term synthesized type
          Same (A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)) ?u0 ?u0
        and is being checked against type
          Same (A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)) ?u0 (sym ?u0)
        but can't determine whether they are equal, since comparing head terms
          ?u0
        and
          sym ?u0
        depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   16 | echo use _ (rf T _)
      ^ can't determine a value for this placeholder
  
   ￫ error[E0401]
   ￭ stdin
   17 | def eqn : Type ≔ let m : T ≔ ? in use m (rf T m)
      ^ term synthesized type
          Same (A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)) m m
        but is being checked against type
          Same (A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)) m (sym m)
        unequal head terms:
          m
        does not equal
          sym m
  
  [1]

A variable can also be sent to a permutation of a variable, since this is invertible, and a permutation of a variable is still neutral.  The solution acts on the variable by the inverse permutation, composed with any permutation of the variable in the value.  Arguments can also be permutations of variables, and are eta-contracted if they agree.

  $ narya -parametric - <<EOF
  > axiom A : Type
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > axiom a₂₀ : Id A a₀₀ a₁₀
  > axiom a₂₁ : Id A a₀₁ a₁₁
  > axiom t : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > def U : Type ≔ Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > def V : Type ≔ Id (Id A) a₂₀ a₂₁ a₀₂ a₁₂
  > def s1 : U → Type ≔ let G : V → U ≔ x ↦ _ in y ↦ let k : Same U (G (sym y)) y ≔ rf U y in Same U y y
  > about s1
  > def s2 (h : U → U) : U → Type ≔ let G : V → U ≔ x ↦ _ in y ↦ let k : Same U (G (sym y)) (h y) ≔ rf U (h y) in Same U y y
  > about s2
  > axiom B : Type
  > axiom b : B
  > axiom g : V → B
  > axiom use1 : (f : V → B) → ((y : U) → Same B (f (sym y)) (g (sym y))) → Type
  > echo use1 _ (y ↦ rf _ (g (sym y)))
  > EOF
  let G ≔ x ↦ sym x in y ↦ let k ≔ rf U y in Same U y y
    : A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁ → Type
  
  h ↦ let G ≔ x ↦ h (sym x) in y ↦ let k ≔ rf U (h y) in Same U y y
    : (h : A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁ → A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁) →
      A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁
      → Type
  
  use1 g (y ↦ rf B (g (sym y)))
    : Type
  

Like other variables, one that is repeated in this way can't be used, even with a different permutation.

  $ narya -parametric - <<EOF
  > axiom A : Type
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > axiom a₂₀ : Id A a₀₀ a₁₀
  > axiom a₂₁ : Id A a₀₁ a₁₁
  > axiom t : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > def U : Type ≔ Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > def V : Type ≔ Id (Id A) a₂₀ a₂₁ a₀₂ a₁₂
  > axiom B : Type
  > axiom b : B
  > axiom k : U → B
  > axiom use1 : (f : V → U → B) → ((y : U) → Same B (f (sym y) y) b) → Type
  > echo use1 _ (y ↦ rf _ b)
  > axiom use2 : (f : V → U → B) → ((y : U) → Same B (f (sym y) y) (k y)) → Type
  > echo use2 _ (y ↦ rf _ (k y))
  > EOF
  use1 (𝑥 𝑦 ↦ b) (y ↦ rf B b)
    : Type
  
   ￫ error[E0406]
   ￭ stdin
   21 | echo use2 _ (y ↦ rf _ (k y))
      ^ term synthesized type
          Same B (k y) (k y)
        and is being checked against type
          Same B (?u2 (sym y) y) (k y)
        but can't determine whether they are equal, since comparing head terms
          k
        and
          ?u2
        depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   21 | echo use2 _ (y ↦ rf _ (k y))
      ^ can't determine a value for this placeholder
  
  [1]

A permutation of a variable isn't the same as that variable, when reading back an occurrence of another metavariable to test whether its environment is the identity.

  $ narya -parametric - <<EOF
  > axiom A : Type
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > axiom a₂₀ : Id A a₀₀ a₁₀
  > axiom a₂₁ : Id A a₀₁ a₁₁
  > axiom t : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > def U : Type ≔ Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > def V : Type ≔ Id (Id A) a₂₀ a₂₁ a₀₂ a₁₂
  > def s : U → Type ≔ let H : U → U ≔ z ↦ _ in let G : V → U ≔ x ↦ _ in y ↦ let k : Same U (G (sym y)) (H y) ≔ rf U (G (sym y)) in let k2 : Same U (H y) y ≔ rf U y in Same U y y
  > about s
  > EOF
  let H ≔ z ↦ z in
  let G ≔ x ↦ let only z : U ≔ sym x in z in
  y ↦
  let k ≔ rf U (G (sym y)) in
  let k2 ≔ rf U y in
  Same U y y
    : A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁ → Type
  

This works for permutations that aren't their own inverse too.

  $ narya -parametric - <<EOF
  > def Top : Type ≔ sig ()
  > 
  > axiom C : Type
  > 
  > axiom c : C
  > 
  > def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig (
  >   a .ungel : R a.0 a.1 )
  > 
  > def R : Top → Top → Type ≔ x y ↦ C
  > 
  > def g : Gel Top Top R () () ≔ (ungel ≔ c)
  > 
  > def t : Top ≔ ()
  > 
  > axiom Same : (X : Type) → X → X → Type
  > 
  > axiom rf : (X : Type) (x : X) → Same X x x
  > 
  > def V : Type
  >   ≔ Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾ t⁽ᵉᵉ⁾ t⁽ᵉᵉ⁾ (refl g) (refl g) (refl g)
  >       (refl g)
  > 
  > def U : Type
  >   ≔ (Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²³¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ t⁽ᵉᵉ⁾
  >       t⁽ᵉᵉ⁾
  > 
  > def s1 : V → Type ≔
  >   let G : U → V ≔ x ↦ _ in
  >   y ↦
  >   let k : Same V (G (y⁽²³¹⁾)) y ≔ rf V y in
  >   Same V y y
  > 
  > about s1
  > 
  > axiom h : V → C
  > 
  > axiom use : (f : U → C) → ((y : V) → Same C (f (y⁽²³¹⁾)) (h y)) → Type
  > 
  > echo use _ (y ↦ rf _ (h y))
  > EOF
  let G ≔ x ↦ x⁽³¹²⁾ in y ↦ let k ≔ rf V y in Same V y y
    : Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾ t⁽ᵉᵉ⁾ t⁽ᵉᵉ⁾ (refl g) (refl g) (refl g)
        (refl g)
      → Type
  
  use (𝑥 ↦ h 𝑥⁽³¹²⁾) (y ↦ rf C (h y))
    : Type
  

A permutation on a metavariable applied to arguments, rather than on the application, also permutes the arguments, including permuting entire cubes of variables.

  $ narya -parametric - <<EOF
  > axiom A : Type
  > 
  > axiom B : Type
  > 
  > axiom f : A → B
  > 
  > axiom Same : (X : Type) → X → X → Type
  > 
  > axiom rf : (X : Type) (x : X) → Same X x x
  > 
  > def T : Type ≔ Id (Id (A → B)) (refl f) (refl f) (refl f) (refl f)
  > 
  > axiom q
  >   : (x00 x01 : A) (x02 : Id A x00 x01) (x10 x11 : A) (x12 : Id A x10 x11)
  >     (x20 : Id A x00 x10) (x21 : Id A x01 x11)
  >     (x22 : Id (Id A) x02 x12 x20 x21)
  >     → B⁽ᵉᵉ⁾ (refl f x02) (refl f x12) (refl f x20) (refl f x21)
  > 
  > axiom use
  >   : (F : T) →
  >     ((x00 x01 : A) (x02 : Id A x00 x01) (x10 x11 : A) (x12 : Id A x10 x11)
  >      (x20 : Id A x00 x10) (x21 : Id A x01 x11)
  >      (x22 : Id (Id A) x02 x12 x20 x21)
  >      → Same (B⁽ᵉᵉ⁾ (refl f x02) (refl f x12) (refl f x20) (refl f x21))
  >          (sym F {x00} {x01} {x02} {x10} {x11} {x12} {x20} {x21} x22)
  >          (q x00 x01 x02 x10 x11 x12 x20 x21 x22))
  >     → Type
  > 
  > echo use _
  >        (x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦
  >         rf _ (q x00 x01 x02 x10 x11 x12 x20 x21 x22))
  > axiom w : T
  > axiom use2 : (F : T) →
  >   ((x00 x01 : A) (x02 : Id A x00 x01) (x10 x11 : A) (x12 : Id A x10 x11)
  >    (x20 : Id A x00 x10) (x21 : Id A x01 x11) (x22 : Id (Id A) x02 x12 x20 x21) →
  >    Same (B⁽ᵉᵉ⁾ (refl f x02) (refl f x12) (refl f x20) (refl f x21))
  >      (sym F {x00} {x01} {x02} {x10} {x11} {x12} {x20} {x21} x22)
  >      (sym w {x00} {x01} {x02} {x10} {x11} {x12} {x20} {x21} x22))
  >   → Type
  > echo use2 _ (x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦ rf _ (sym w {x00} {x01} {x02} {x10} {x11} {x12} {x20} {x21} x22))
  > EOF
  use (𝑥 ⤇ sym (q 𝑥.00 𝑥.10 𝑥.20 𝑥.01 𝑥.11 𝑥.21 𝑥.02 𝑥.12 (sym 𝑥.22)))
    (x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦
     rf (B⁽ᵉᵉ⁾ (ap f x02) (ap f x12) (ap f x20) (ap f x21))
       (q x00 x01 x02 x10 x11 x12 x20 x21 x22))
    : Type
  
  use2 w
    (x00 x01 x02 x10 x11 x12 x20 x21 x22 ↦
     rf (B⁽ᵉᵉ⁾ (ap f x02) (ap f x12) (ap f x20) (ap f x21)) (sym w x22))
    : Type
  

A projection from a metavariable with a permutation on it, or on its application to arguments, expands it to the inverse permutation of a tuple.

  $ narya -parametric - <<EOF
  > def Top : Type ≔ sig ()
  > axiom C : Type
  > axiom c : C
  > axiom cc : Id C c c
  > def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig ( a .ungel : R a.0 a.1 )
  > def R : Top → Top → Type ≔ x y ↦ C
  > def g : Gel Top Top R () () ≔ (ungel ≔ c)
  > def t : Top ≔ ()
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > def U : Type ≔ (Gel Top Top R)⁽ᵉ¹⁾ {t} {t} g {t} {t} g (refl t) (refl t)
  > axiom use : (m : U) → Same (Id C c c) (sym m .ungel) cc → Type
  > echo use _ (rf _ cc)
  > axiom A : Type
  > axiom cca : A → Id C c c
  > axiom use2 : (f : A → U) → ((x : A) → Same (Id C c c) (sym (f x) .ungel) (cca x)) → Type
  > echo use2 _ (x ↦ rf _ (cca x))
  > EOF
  use (sym (ungel ≔ cc)) (rf (Id C c c) cc)
    : Type
  
  use2 (𝑥 ↦ sym (ungel ≔ cca 𝑥)) (x ↦ rf (Id C c c) (cca x))
    : Type
  

This works for permutations that aren't their own inverse too.

  $ narya -parametric - <<EOF
  > def Top : Type ≔ sig ()
  > axiom C : Type
  > axiom c : C
  > axiom ccc : C⁽ᵉᵉ⁾ (refl c) (refl c) (refl c) (refl c)
  > def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig ( a .ungel : R a.0 a.1 )
  > def R : Top → Top → Type ≔ x y ↦ C
  > def g : Gel Top Top R () () ≔ (ungel ≔ c)
  > def t : Top ≔ ()
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > def U : Type ≔ (Gel⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ Top⁽ᵉᵉ⁾ R⁽ᵉᵉ⁾)⁽²³¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ g⁽ᵉ¹⁾ t⁽ᵉᵉ⁾ t⁽ᵉᵉ⁾
  > axiom use : (m : U) → Same (C⁽ᵉᵉ⁾ (refl c) (refl c) (refl c) (refl c)) (m⁽³¹²⁾ .ungel) ccc → Type
  > echo use _ (rf _ ccc)
  > EOF
  use (ungel ≔ ccc)⁽²³¹⁾ (rf (C⁽ᵉᵉ⁾ (refl c) (refl c) (refl c) (refl c)) ccc)
    : Type
  

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
  

An instantiation of a degenerated metavariable isn't a place where the metavariable can be solved directly, and its type doesn't mention the metavariable.  But the instantiation arguments are determined by the type, and their types do mention the metavariable.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom a₃ : A
  > axiom s : (X : Type) (x y : X) → Id X x y → Id X y x
  > echo s _ _ _ a₂
  > axiom B : Type
  > axiom f : A → B
  > axiom g : A → B
  > axiom h : Id (A → B) f g
  > echo s _ _ _ h
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > axiom a₂₀ : Id A a₀₀ a₁₀
  > axiom a₂₁ : Id A a₀₁ a₁₁
  > axiom t : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > axiom s2 : (X : Type) (x00 x01 : X) (x02 : Id X x00 x01) (x10 x11 : X) (x12 : Id X x10 x11) (x20 : Id X x00 x10) (x21 : Id X x01 x11) → Id (Id X) x02 x12 x20 x21 → X
  > echo s2 _ _ _ _ _ _ _ _ _ t
  > EOF
  s A a₀ a₁ a₂
    : Id A a₁ a₀
  
  s (A → B) f g h
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id B (g 𝑥₀) (f 𝑥₁)
  
  s2 A a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ t
    : A
  

An instantiation is determined even if the metavariable in the head is the same, in which case the arguments can be equated although the metavariable remains unknown.

  $ narya - <<EOF
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > axiom use : (X : Type) (x y z w : X) → Same Type (Id X x y) (Id X z w) → Type
  > echo use _ _ _ _ _ (rf _ _)
  > EOF
   ￫ error[E2004]
   ￭ stdin
   4 | echo use _ _ _ _ _ (rf _ _)
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   4 | echo use _ _ _ _ _ (rf _ _)
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   4 | echo use _ _ _ _ _ (rf _ _)
     ^ can't determine a value for this placeholder
  
  [1]

They can also be unequal.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom a₃ : A
  > axiom s : (X : Type) (x y : X) → Id X x y → Id X y x
  > echo s _ a₃ _ a₂
  > EOF
   ￫ error[E0401]
   ￭ stdin
   7 | echo s _ a₃ _ a₂
     ^ term synthesized type
         Id A a₀ a₁
       but is being checked against type
         Id A a₃ ?u1
       unequal head constants:
         a₀
       does not equal
         a₃
  
  [1]

Since instantiation is generative, this can also solve a metavariable that is itself a higher-dimensional type.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom Same : (X : Type) → X → X → Type
  > axiom rf : (X : Type) (x : X) → Same X x x
  > axiom use : (F : Id Type A A) (x y : A) → Same Type (F x y) (Id A a₀ a₁) → Type
  > echo use _ _ _ (rf _ (Id A a₀ a₁))
  > EOF
  use (Id A) a₀ a₁ (rf Type (Id A a₀ a₁))
    : Type
  

A degeneracy of a placeholder that is applied to arguments, using the name of the degeneracy for types, is a degeneracy of a placeholder for a zero-dimensional type.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > axiom a₂₀ : Id A a₀₀ a₁₀
  > axiom a₂₁ : Id A a₀₁ a₁₁
  > axiom t : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > echo a₂ : Id _ a₀ a₁
  > echo a₂ : Id _ _ _
  > echo t : Id (Id _) a₀₂ a₁₂ a₂₀ a₂₁
  > def f (x : A) : Id _ x x ≔ refl x
  > echo f a₀
  > EOF
  a₂
    : Id A a₀ a₁
  
  a₂
    : Id A a₀ a₁
  
  t
    : A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁
  
  refl a₀
    : Id A a₀ a₀
  

This uses the same name that is displayed for degeneracies of types, which can be changed.

  $ narya -parametric -direction p,rel,Br - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Br A a₀ a₁
  > echo a₂ : Br _ a₀ a₁
  > EOF
  a₂
    : Br A a₀ a₁
  

Its other names and its superscript don't do this, since they could also be degeneracies of functions.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom f : A → A
  > echo a₂ : refl _ a₀ a₁
  > echo a₂ : ap _ a₀ a₁
  > echo a₂ : _⁽ᵉ⁾ a₀ a₁
  > echo refl _ a₂ : Id A (f a₀) (f a₁)
  > EOF
   ￫ error[E0400]
   ￭ stdin
   6 | echo a₂ : refl _ a₀ a₁
     ^ non-synthesizing term in synthesizing position (degeneracy of placeholder function)
  
   ￫ error[E0400]
   ￭ stdin
   7 | echo a₂ : ap _ a₀ a₁
     ^ non-synthesizing term in synthesizing position (degeneracy of placeholder function)
  
   ￫ error[E0400]
   ￭ stdin
   8 | echo a₂ : _⁽ᵉ⁾ a₀ a₁
     ^ non-synthesizing term in synthesizing position (degeneracy of placeholder function)
  
   ￫ error[E0400]
   ￭ stdin
   9 | echo refl _ a₂ : Id A (f a₀) (f a₁)
     ^ non-synthesizing term in synthesizing position (degeneracy of placeholder function)
  
  [1]

The dimension of the placeholder is determined by the number of explicit arguments, assuming that the type is fully instantiated.  Thus, it can be a higher-dimensional type that isn't a degeneracy of anything, and can be solved by comparing it with one.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > axiom a₂₀ : Id A a₀₀ a₁₀
  > axiom a₂₁ : Id A a₀₁ a₁₁
  > axiom t : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁
  > echo t : Id _ a₀₂ a₁₂ a₂₀ a₂₁
  > echo t : Id _ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁
  > echo t : Id _ {_} {_} _ {_} {_} _ _ _
  > EOF
  t
    : A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁
  
  t
    : A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁
  
  t
    : A⁽ᵉᵉ⁾ a₀₂ a₁₂ a₂₀ a₂₁
  

  $ narya -parametric - <<EOF
  > axiom A : Type
  > axiom B : Type
  > axiom R : A → B → Type
  > def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig ( a .ungel : R a.0 a.1 )
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom b₀ : B
  > axiom b₁ : B
  > axiom b₂ : Id B b₀ b₁
  > axiom x₀ : Gel A B R a₀ b₀
  > axiom x₁ : Gel A B R a₁ b₁
  > axiom t : Id (Gel A B R) a₂ b₂ x₀ x₁
  > echo t : Id _ a₂ b₂ x₀ x₁
  > EOF
  t
    : Gel⁽ᵉ⁾ (Id A) (Id B) (Id R) a₂ b₂ x₀ x₁
  

The number of arguments for a given dimension depends on the arity.

  $ narya -arity 1 -direction r,refl,Id -parametric - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : Id A a₀
  > axiom a₂ : Id (Id A) a₁ a₁
  > echo a₁ : Id _ a₀
  > echo a₂ : Id _ a₁ a₁
  > EOF
  a₁
    : Id A a₀
  
  a₂
    : A⁽ʳʳ⁾ a₁ a₁
  

  $ narya -parametric -arity 3 -direction r,refl,Id - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : Id A a₀ a₀ a₀
  > echo a₁ : Id _ a₀ a₀ a₀
  > EOF
  a₁
    : Id A a₀ a₀ a₀
  

With arity zero, however, there is no boundary to determine the placeholder.

  $ narya -parametric -arity 0 -direction w,wk,Wk - <<EOF
  > axiom A : Type
  > axiom a : Wk A .
  > echo a : Wk _ .
  > EOF
   ￫ error[E0406]
   ￭ stdin
   3 | echo a : Wk _ .
     ^ term synthesized type
         Wk A .
       and is being checked against type
         wk ?u0 .
       but can't determine whether they are equal, since comparing head terms
         Wk A
       and
         wk ?u0
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   3 | echo a : Wk _ .
     ^ can't determine a value for this placeholder
  
  [1]

If the type is only partially instantiated, the placeholder has the wrong dimension, and has to be given by hand.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀₀ : A
  > axiom a₀₁ : A
  > axiom a₀₂ : Id A a₀₀ a₀₁
  > axiom a₁₀ : A
  > axiom a₁₁ : A
  > axiom a₁₂ : Id A a₁₀ a₁₁
  > echo Id (Id A) a₀₂ a₁₂
  > echo Id (Id _) a₀₂ a₁₂
  > echo Id _ a₀₂ a₁₂
  > EOF
  A⁽ᵉᵉ⁾ a₀₂ a₁₂
    : Type⁽ᵉ⁾ (Id A a₀₀ a₁₀) (Id A a₀₁ a₁₁)
  
  A⁽ᵉᵉ⁾ a₀₂ a₁₂
    : Type⁽ᵉ⁾ (Id A a₀₀ a₁₀) (Id A a₀₁ a₁₁)
  
   ￫ error[E0401]
   ￭ stdin
   10 | echo Id _ a₀₂ a₁₂
      ^ term synthesized type
          Id A a₁₀ a₁₁
        but is being checked against type
          Id A a₀₀ a₀₁
        unequal head constants:
          a₁₀
        does not equal
          a₀₀
  
  [1]

A primary argument that doesn't synthesize can't supply its implicit boundary, so that boundary is filled with placeholders, as if the user had written them.  Then something else has to determine them, such as the type being checked against, or the components of a tuple or abstraction.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom t : Id (Id A) a₂ a₂ (refl a₀) (refl a₁)
  > echo t : Id _ _ _ _ _
  > echo t : Id (Id A) _ _ _ _
  > axiom B : Type
  > axiom b₀ : B
  > axiom b₁ : B
  > axiom b₂ : Id B b₀ b₁
  > def S : Type ≔ sig ( fst : A, snd : B )
  > axiom f : S → A
  > echo refl f (fst ≔ a₂, snd ≔ b₂)
  > axiom h : (A → A) → A
  > echo refl h (x ⤇ x.2)
  > EOF
  t
    : A⁽ᵉᵉ⁾ a₂ a₂ (refl a₀) (refl a₁)
  
  t
    : A⁽ᵉᵉ⁾ a₂ a₂ (refl a₀) (refl a₁)
  
  ap f {(fst ≔ a₀, snd ≔ b₀)} {(fst ≔ a₁, snd ≔ b₁)} (fst ≔ a₂, snd ≔ b₂)
    : Id A (f (fst ≔ a₀, snd ≔ b₀)) (f (fst ≔ a₁, snd ≔ b₁))
  
  ap h {𝑥 ↦ 𝑥} {𝑥 ↦ 𝑥} (x ⤇ x.2)
    : Id A (h (𝑥 ↦ 𝑥)) (h (𝑥 ↦ 𝑥))
  

A solved metavariable in the boundary of the codomain of a higher function-type has an environment that uses the whole cube of variables, but its solution doesn't have to.

  $ narya - <<EOF
  > axiom A : Type
  > axiom C : Type
  > def S : Type ≔ sig ( fst : A, snd : C )
  > axiom G : S → Type
  > echo (x : Id S) ⇒ Id G x.2
  > echo (x : Id S) ⇒ Id G (fst ≔ x.2 .fst, snd ≔ x.2 .snd)
  > EOF
  (x : S⁽ᵉ⁾) ⇒ Id G x.2
    : Type⁽ᵉ⁾ ((x : S) → G x) ((x : S) → G x)
  
  (x : S⁽ᵉ⁾)
  ⇒ Id G {(fst ≔ x.0 .fst, snd ≔ x.0 .snd)}
      {(fst ≔ x.1 .fst, snd ≔ x.1 .snd)} (fst ≔ x.2 .fst, snd ≔ x.2 .snd)
    : Type⁽ᵉ⁾ ((x : S) → G (fst ≔ x .fst, snd ≔ x .snd))
        ((x : S) → G (fst ≔ x .fst, snd ≔ x .snd))
  

This also applies to a primary argument that looks like it synthesizes, but doesn't have all the synthesizing subterms it would need to.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom f : A → A
  > echo refl f (refl _) : Id A (f a₀) (f a₀)
  > axiom t : Id (Id A) a₂ a₂ (refl a₀) (refl a₁)
  > echo t : Id (Id A) _ _ (refl _) _
  > axiom B : Type
  > axiom b₀ : B
  > axiom b₁ : B
  > axiom b₂ : Id B b₀ b₁
  > def S : Type ≔ sig ( fst : A, snd : B )
  > axiom g : S → A
  > echo refl g (let z ≔ a₂ in (fst ≔ z, snd ≔ b₂))
  > axiom h : (A → A) → A
  > echo refl h (refl (y ↦ y))
  > EOF
  ap f (refl a₀)
    : Id A (f a₀) (f a₀)
  
  t
    : A⁽ᵉᵉ⁾ a₂ a₂ (refl a₀) (refl a₁)
  
  ap g {(fst ≔ a₀, snd ≔ b₀)} {(fst ≔ a₁, snd ≔ b₁)} (fst ≔ a₂, snd ≔ b₂)
    : Id A (g (fst ≔ a₀, snd ≔ b₀)) (g (fst ≔ a₁, snd ≔ b₁))
  
  ap h {y ↦ y} {y ↦ y} (y ⤇ y.2)
    : Id A (h (y ↦ y)) (h (y ↦ y))
  

But one that does have them is still synthesized.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > axiom f : A → A
  > echo refl f (let z ≔ a₀ in a₂)
  > EOF
  ap f a₂
    : Id A (f a₀) (f a₁)
  

If nothing determines them, then the primary argument didn't have enough information.

  $ narya - <<EOF
  > axiom A : Type
  > axiom f : A → A
  > echo refl f ?
  > EOF
   ￫ error[E0400]
   ￭ stdin
   3 | echo refl f ?
     ^ non-synthesizing term in synthesizing position (primary argument with implicit higher-dimensional application boundaries)
  
  [1]

  $ narya - <<EOF
  > axiom A : Type
  > axiom f : A → A
  > echo refl f _
  > EOF
   ￫ error[E0400]
   ￭ stdin
   3 | echo refl f _
     ^ non-synthesizing term in synthesizing position (primary argument with implicit higher-dimensional application boundaries)
  
  [1]

Every unsolved metavariable with a different location is reported, while metavariables created together for the same term are reported once.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a : A
  > def Pr : Type ≔ sig ( fst : A, snd : A )
  > axiom g : A → A → A
  > echo g _ a
  > echo g _ _
  > def two : Pr ≔ let p : Pr ≔ _ in p
  > EOF
   ￫ error[E2004]
   ￭ stdin
   5 | echo g _ a
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   6 | echo g _ _
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   6 | echo g _ _
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   7 | def two : Pr ≔ let p : Pr ≔ _ in p
     ^ can't determine a value for this placeholder
  
  [1]

A constructor can determine them too, since its boundary must consist of instances of the same constructor.  So if a metavariable appears in that boundary, it is solved by an application of that constructor to new metavariables.

  $ narya - <<EOF
  > axiom A : Type
  > def N : Type ≔ data [ zero. | suc. (_ : N) ]
  > axiom g : N → A
  > axiom n₀ : N
  > axiom n₁ : N
  > axiom n₂ : Id N n₀ n₁
  > echo refl g (suc. n₂)
  > echo refl g zero.
  > echo refl g (suc. (suc. n₂))
  > echo suc. n₂ : Id N _ _
  > axiom n₀₀ : N
  > axiom n₀₁ : N
  > axiom n₀₂ : Id N n₀₀ n₀₁
  > axiom n₁₀ : N
  > axiom n₁₁ : N
  > axiom n₁₂ : Id N n₁₀ n₁₁
  > axiom n₂₀ : Id N n₀₀ n₁₀
  > axiom n₂₁ : Id N n₀₁ n₁₁
  > axiom t : Id (Id N) n₀₂ n₁₂ n₂₀ n₂₁
  > echo suc. t : Id (Id N) _ _ _ _
  > def Vec (T : Type) : N → Type ≔ data [ nil. : Vec T zero. | cons. (n : N) (x : T) (xs : Vec T n) : Vec T (suc. n) ]
  > axiom a₀ : A
  > axiom a₁ : A
  > axiom a₂ : Id A a₀ a₁
  > echo nil. : Id (Vec A zero.) _ _
  > axiom v₀ : Vec A n₀
  > axiom v₁ : Vec A n₁
  > axiom v₂ : Id (Vec A) n₂ v₀ v₁
  > echo cons. n₂ a₂ v₂ : Id (Vec A) (suc. n₂) _ _
  > EOF
  ap g {suc. n₀} {suc. n₁} (suc. n₂)
    : Id A (g (suc. n₀)) (g (suc. n₁))
  
  ap g {0} {0} (refl 0)
    : Id A (g 0) (g 0)
  
  ap g {suc. (suc. n₀)} {suc. (suc. n₁)} (suc. (suc. n₂))
    : Id A (g (suc. (suc. n₀))) (g (suc. (suc. n₁)))
  
  suc. n₂
    : N⁽ᵉ⁾ (suc. n₀) (suc. n₁)
  
  suc. t
    : N⁽ᵉᵉ⁾ {suc. n₀₀} {suc. n₀₁} (suc. n₀₂) {suc. n₁₀} {suc. n₁₁} (suc. n₁₂)
        (suc. n₂₀) (suc. n₂₁)
  
  nil.
    : Vec⁽ᵉ⁾ (Id A) {0} {0} (refl 0) nil. nil.
  
  cons. n₂ a₂ v₂
    : Vec⁽ᵉ⁾ (Id A) {suc. n₀} {suc. n₁} (suc. n₂) (cons. n₀ a₀ v₀)
        (cons. n₁ a₁ v₁)
  

This also works when the environment of the metavariable is a renaming, or it is applied to variables, since then a substitution can't produce a constructor from something else.

  $ narya - <<EOF
  > axiom A : Type
  > def N : Type ≔ data [ zero. | suc. (_ : N) ]
  > def ren : N → Type ≔ let G : N → N ≔ x ↦ _ in y ↦ let p : Id N (G y) (suc. y) ≔ suc. (refl y) in A
  > about ren
  > axiom use : (f : N → N) → ((y : N) → Id N (f y) (suc. y)) → Type
  > echo use _ (y ↦ suc. (refl y))
  > EOF
  let G ≔ x ↦ suc. x in y ↦ let p ≔ suc. (refl y) in A
    : N → Type
  
  use (𝑥 ↦ suc. 𝑥) (y ↦ suc. (refl y))
    : Type
  

But not otherwise, since then the metavariable could be something that is not a constructor.

  $ narya - <<EOF
  > axiom A : Type
  > def N : Type ≔ data [ zero. | suc. (_ : N) ]
  > def nonren (y : N) : Type ≔ let G : N → N ≔ x ↦ _ in let p : Id N (G (suc. y)) (G (suc. y)) ≔ suc. (refl y) in A
  > EOF
   ￫ error[E1002]
   ￭ stdin
   3 | def nonren (y : N) : Type ≔ let G : N → N ≔ x ↦ _ in let p : Id N (G (suc. y)) (G (suc. y)) ≔ suc. (refl y) in A
     ^ instantiation arguments of datatype must be matching constructors:
       expected
         suc
       but got
         let only … in ?u0
  
  [1]

And the boundary must still consist of the same constructor.

  $ narya - <<EOF
  > def N : Type ≔ data [ zero. | suc. (_ : N) ]
  > axiom n₀ : N
  > axiom n₁ : N
  > axiom n₂ : Id N n₀ n₁
  > echo suc. n₂ : Id N _ zero.
  > EOF
   ￫ error[E1002]
   ￭ stdin
   5 | echo suc. n₂ : Id N _ zero.
     ^ instantiation arguments of datatype must be matching constructors:
       expected
         suc
       but got
         zero
  
  [1]


A degeneracy can act on a term whose type is a metavariable, and that metavariable can be solved later.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a : A
  > axiom use : Id A a a → Type
  > def t : Type ≔ let x ≔ refl (_ : _) in use x
  > echo t
  > EOF
  use (refl a)
    : Type
  

  $ narya -parametric -arity 1 -direction d -external -discrete-tconn - <<EOF
  > axiom A : Type
  > axiom a : A
  > echo (_ : _)⁽ᵈ⁾ : A⁽ᵈ⁾ a
  > EOF
  a⁽ᵈ⁾
    : A⁽ᵈ⁾ a
  

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
  
   ￫ error[E0406]
   ￭ stdin
   5 | def s' : A ≔ let X : Type ≔ _ in (a : id X A)
     ^ term synthesized type
         Type
       and is being checked against type
         X
       but can't determine whether they are equal, since comparing head terms
         Type
       and
         X
       depends on unsolved placeholders
  
   ￫ error[E0406]
   ￭ stdin
   5 | def s' : A ≔ let X : Type ≔ _ in (a : id X A)
     ^ term synthesized type
         X
       and is being checked against type
         Type
       but can't determine whether they are equal, since comparing head terms
         X
       and
         Type
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   5 | def s' : A ≔ let X : Type ≔ _ in (a : id X A)
     ^ can't determine a value for this placeholder
  
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
  
   ￫ info[I0000]
   ￮ constant v defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ error[E0406]
   ￭ stdin
   5 | def F (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ term synthesized type
         B a
       and is being checked against type
         B (let only … in ?u3)
       but can't determine whether they are equal, since comparing head terms
         a
       and
         let only … in ?u3
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   5 | def F (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ can't determine a value for this placeholder
  
   ￫ info[I0101]
   ￮ display set let to environments
  
   ￫ error[E0406]
   ￭ stdin
   7 | def F' (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ term synthesized type
         B a
       and is being checked against type
         B (let only a : A ≔ a and b : B a ≔ b and x : A ≔ a in ?u5)
       but can't determine whether they are equal, since comparing head terms
         a
       and
         let only a : A ≔ a and b : B a ≔ b and x : A ≔ a in ?u5
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   7 | def F' (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   8 | def H (a : A) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a → G a ≔ y ↦ y in A
     ^ can't determine a value for this placeholder
  
  [1]

If the synthesized type of a term can't yet be compared to the type it is checked against, because the comparison is stuck on a metavariable, the term is replaced by a delayed metavariable and the comparison is postponed.  Here ?F a0 =? B a0 is stuck, since a0 is not a variable, but a later comparison solves ?F, so the postponed comparison succeeds and releases the term.  Postponed comparisons in a chain, in the branches of a match, at a case tree leaf, and with an ascription work the same way.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a0 : A
  > axiom a1 : A
  > axiom B : A → Type
  > axiom b : B a0
  > axiom b1 : B a1
  > axiom g : B a0 → A
  > def Bool : Type ≔ data [ true. | false. ]
  > def ok : Type ≔ let F : A → Type ≔ _ in let y : F a0 ≔ b in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in A
  > echo let F : A → Type ≔ _ in let y : F a0 ≔ b in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in y
  > def chain : A ≔ let F : A → Type ≔ _ in let y : F a0 ≔ b in let z : B a0 ≔ y in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in g z
  > echo let F : A → Type ≔ _ in let y : F a0 ≔ b in let z : B a0 ≔ y in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in g z
  > def br (c : Bool) : A ≔ let F : A → Type ≔ _ in let y : F a0 ≔ match c [ true. ↦ b | false. ↦ b ] in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in g y
  > def leaf (c : Bool) : B a0 ≔ let F : A → Type ≔ _ in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in match c [ true. ↦ (b : F a0) | false. ↦ b ]
  > def asc : A ≔ let F : A → Type ≔ _ in let y ≔ (b : F a0) in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in g y
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom b1 assumed
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant ok defined
  
  b
    : B a0
  
   ￫ info[I0000]
   ￮ constant chain defined
  
  g b
    : A
  
   ￫ info[I0000]
   ￮ constant br defined
  
   ￫ info[I0000]
   ￮ constant leaf defined
  
   ￫ info[I0000]
   ￮ constant asc defined
  

When the postponed comparison is retried, it may turn out to fail, which is reported at the term.  If it can never be decided, that is reported along with the metavariables it is stuck on.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a0 : A
  > axiom a1 : A
  > axiom B : A → Type
  > axiom b : B a0
  > axiom b1 : B a1
  > axiom g : B a0 → A
  > def Bool : Type ≔ data [ true. | false. ]
  > def bad : Type ≔ let F : A → Type ≔ _ in let y : F a0 ≔ b1 in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in A
  > def brbad (c : Bool) : A ≔ let F : A → Type ≔ _ in let y : F a0 ≔ match c [ true. ↦ b | false. ↦ b1 ] in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in g y
  > def left : Type ≔ let F : A → Type ≔ _ in let y : F a0 ≔ b in A
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom b1 assumed
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ error[E0401]
   ￭ stdin
   9 | def bad : Type ≔ let F : A → Type ≔ _ in let y : F a0 ≔ b1 in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in A
     ^ term synthesized type
         B a1
       but is being checked against type
         B a0
       unequal head constants:
         a1
       does not equal
         a0
  
   ￫ error[E0401]
   ￭ stdin
   10 | def brbad (c : Bool) : A ≔ let F : A → Type ≔ _ in let y : F a0 ≔ match c [ true. ↦ b | false. ↦ b1 ] in let k : (x : A) → Id Type (F x) (B x) ≔ x ↦ refl (B x) in g y
      ^ term synthesized type
          B a1
        but is being checked against type
          B a0
        unequal head constants:
          a1
        does not equal
          a0
  
   ￫ error[E0406]
   ￭ stdin
   11 | def left : Type ≔ let F : A → Type ≔ _ in let y : F a0 ≔ b in A
      ^ term synthesized type
          B a0
        and is being checked against type
          F a0
        but can't determine whether they are equal, since comparing head terms
          B
        and
          F
        depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   11 | def left : Type ≔ let F : A → Type ≔ _ in let y : F a0 ≔ b in A
      ^ can't determine a value for this placeholder
  
  [1]

A comparison that is stuck is still unequal if the metavariable can't be solved however other metavariables are solved, because the value contains the metavariable itself or a variable outside its scope in a rigid position (see the examples above).  But a variable at a singleton type isn't rigid, since anything else of that type could replace it, so this is undetermined rather than unequal (even though ?X := c () would be a solution).

  $ narya -v - <<EOF
  > axiom A : Type
  > def Unit : Type ≔ sig ()
  > axiom c : Unit → A
  > def sing (k : (X : A) → ((u : Unit) → Id A X (c u)) → Type) : Type ≔ k _ (u ↦ refl (c u))
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant Unit defined
  
   ￫ info[I0001]
   ￮ axiom c assumed
  
   ￫ error[E0406]
   ￭ stdin
   4 | def sing (k : (X : A) → ((u : Unit) → Id A X (c u)) → Type) : Type ≔ k _ (u ↦ refl (c u))
     ^ term synthesized type
         Id A (c u) (c u)
       and is being checked against type
         Id A ?u0 (c u)
       but can't determine whether they are equal, since comparing head terms
         c
       and
         ?u0
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   4 | def sing (k : (X : A) → ((u : Unit) → Id A X (c u)) → Type) : Type ≔ k _ (u ↦ refl (c u))
     ^ can't determine a value for this placeholder
  
  [1]

A delayed metavariable displayed in a message is shown by name, with a remark pointing to the term it stands for.  Here the occurrence of T is checked at Type, but its type F A can't be compared to Type yet, so it is guarded.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a0 : A
  > axiom P : Type → Type
  > def t : Type ≔
  >   let F : Type → Type ≔ _ in
  >   let T : F A ≔ A in
  >   let z : P T ≔
  >     a0 in
  >   A
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom P assumed
  
   ￫ error[E0401]
   ￭ stdin
   7 |   let z : P T ≔
     ^ ?u2 stands for this term, whose type hasn't been checked yet
   8 |     a0 in
     ^ term synthesized type
         A
       but is being checked against type
         P ?u2
       unequal head constants:
         A
       does not equal
         P
  
  [1]

A term that can only be checked against a type of a particular shape, such as an abstraction or a tuple, can't be checked yet against a type that is stuck on a metavariable.  Then checking it is postponed, and retried once the type is known, which may reveal an error.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a : A
  > def t2 : A ≔ let T : Type ≔ _ in let h : T ≔ x ↦ x in (h : A → A) a
  > def t4 : A ≔ let T : Type ≔ _ in let h : T ≔ x ↦ x in let k : Id Type T (A → A) ≔ refl (A → A) in h a
  > echo let T : Type ≔ _ in let h : T ≔ x ↦ x in let k : Id Type T (A → A) ≔ refl (A → A) in h
  > def bad : A ≔ let T : Type ≔ _ in let h : T ≔ x ↦ x in let k : Id Type T A ≔ refl A in a
  > def t3 : A ≔ let T : Type ≔ _ in let h : T ≔ (a, a) in a
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant t2 defined
  
   ￫ info[I0000]
   ￮ constant t4 defined
  
  x ↦ x
    : A → A
  
   ￫ error[E0700]
   ￭ stdin
   6 | def bad : A ≔ let T : Type ≔ _ in let h : T ≔ x ↦ x in let k : Id Type T A ≔ refl A in a
     ^ checking abstraction against non-function type A
  
   ￫ error[E0407]
   ￭ stdin
   7 | def t3 : A ≔ let T : Type ≔ _ in let h : T ≔ (a, a) in a
     ^ can't check this term against type
         T
       since what kind of type it is depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   7 | def t3 : A ≔ let T : Type ≔ _ in let h : T ≔ (a, a) in a
     ^ can't determine a value for this placeholder
  
  [1]

Likewise, applying a function or projecting a field from a term whose type is stuck on a metavariable is postponed.  Its result gets a new metavariable as its type, which later comparisons can solve, and which is compared to the actual type once the application or projection can be done.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a : A
  > axiom h : A → A
  > axiom B : Type
  > axiom hb : B → B
  > axiom f2 : (X : Type) → (X → A) → X → A
  > def P : Type ≔ sig (fst : A, snd : A)
  > axiom p : P
  > def t1 : A ≔ f2 _ (g ↦ g a) h
  > echo f2 _ (g ↦ g a) h
  > def t2 : A ≔ f2 _ (g ↦ g (g a)) h
  > def t3 : A ≔ f2 _ (g ↦ g .fst) p
  > def t4 : A ≔ f2 _ (g ↦ g a .fst) h
  > def bad : A ≔ f2 _ (g ↦ g a) hb
  > def und : A ≔ let T : Type ≔ _ in let x : T ≔ _ in x .fst
  > def und2 : A ≔ f2 _ (g ↦ g a) (x ↦ x)
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom h assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom hb assumed
  
   ￫ info[I0001]
   ￮ axiom f2 assumed
  
   ￫ info[I0000]
   ￮ constant P defined
  
   ￫ info[I0001]
   ￮ axiom p assumed
  
   ￫ info[I0000]
   ￮ constant t1 defined
  
  f2 (A → A) (g ↦ g a) h
    : A
  
   ￫ info[I0000]
   ￮ constant t2 defined
  
   ￫ info[I0000]
   ￮ constant t3 defined
  
   ￫ error[E0800]
   ￭ stdin
   13 | def t4 : A ≔ f2 _ (g ↦ g a .fst) h
      ^ term g a has no field named fst
  
   ￫ error[E0401]
   ￭ stdin
   14 | def bad : A ≔ f2 _ (g ↦ g a) hb
      ^ term synthesized type
          A
        but is being checked against type
          B
        unequal head constants:
          A
        does not equal
          B
  
   ￫ error[E0401]
   ￭ stdin
   14 | def bad : A ≔ f2 _ (g ↦ g a) hb
      ^ term synthesized type
          B
        but is being checked against type
          A
        unequal head constants:
          B
        does not equal
          A
  
   ￫ error[E0409]
   ￭ stdin
   15 | def und : A ≔ let T : Type ≔ _ in let x : T ≔ _ in x .fst
      ^ can't project field fst from
          x
        of type
          T
        since what kind of type it is depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   15 | def und : A ≔ let T : Type ≔ _ in let x : T ≔ _ in x .fst
      ^ can't determine a value for this placeholder
  
   ￫ error[E2004]
   ￭ stdin
   15 | def und : A ≔ let T : Type ≔ _ in let x : T ≔ _ in x .fst
      ^ can't determine a value for this placeholder
  
   ￫ error[E0407]
   ￭ stdin
   16 | def und2 : A ≔ f2 _ (g ↦ g a) (x ↦ x)
      ^ can't check this term against type
          ?u24
        since what kind of type it is depends on unsolved placeholders
  
   ￫ error[E0408]
   ￭ stdin
   16 | def und2 : A ≔ f2 _ (g ↦ g a) (x ↦ x)
      ^ can't apply/instantiate
          g
        of type
          ?u24
        since what kind of type it is depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   16 | def und2 : A ≔ f2 _ (g ↦ g a) (x ↦ x)
      ^ can't determine a value for this placeholder
  
  [1]

Before a comparison or another decision treats something stuck as a failure, or postpones it, the postponed constraints whose metavariables have since been solved are retried, in case that unsticks it.  Here T is guarded until F is solved, and the matches need to know that T is a datatype.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a : A
  > def Bool : Type ≔ data [ true. | false. ]
  > def t1 (b : Bool) : A ≔
  >   let F : Type → Type ≔ _ in
  >   let T : F Type ≔ Bool in
  >   let k : Id (Type → Type) F (X ↦ X) ≔ refl (X ↦ X) in
  >   let c : T ≔ b in
  >   match c [ true. ↦ a | false. ↦ a ]
  > def t2 : Bool → A ≔
  >   let F : Type → Type ≔ _ in
  >   let T : F Type ≔ Bool in
  >   let k : Id (Type → Type) F (X ↦ X) ≔ refl (X ↦ X) in
  >   let g : T → A ≔ x ↦ match x [ true. ↦ a | false. ↦ a ] in
  >   g
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ hint[E1101]
   ￭ stdin
   9 |   match c [ true. ↦ a | false. ↦ a ]
     ^ match will not refine the goal or context (discriminee is let-bound): c
  
   ￫ info[I0000]
   ￮ constant t1 defined
  
   ￫ info[I0000]
   ￮ constant t2 defined
  

Whether a match against a variable can refine the goal and context depends on its indices being distinct free variables that don't occur in its parameters.  If that depends on unsolved metavariables, then postponed constraints are retried first.  If an index is still stuck, we can't tell, so this is an error (unless another index already prevents refining); "return _" gives a non-refining match instead.  If the parameters might involve the indices only through unsolved metavariables, the match refines, and we check later that they don't.

  $ narya -v - <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def Vec (A : Type) : ℕ → Type ≔ data [ nil. : Vec A zero. | cons. (n : ℕ) (x : A) (xs : Vec A n) : Vec A (suc. n) ]
  > def f (n : ℕ) : ℕ ≔ let A : Type ≔ _ in let g : Vec A n → ℕ ≔ v ↦ match v [ nil. ↦ zero. | cons. k x xs ↦ zero. ] in let e : Id Type A ℕ ≔ refl ℕ in zero.
  > def f2 (n : ℕ) : ℕ ≔ let A : Type ≔ _ in let g : Vec A n → ℕ ≔ v ↦ match v [ nil. ↦ zero. | cons. k x xs ↦ zero. ] in let e : Id Type A (Vec ℕ n) ≔ refl (Vec ℕ n) in zero.
  > def f3 (m : ℕ) : ℕ ≔ let N : ℕ ≔ _ in let g : Vec ℕ N → ℕ ≔ v ↦ match v [ nil. ↦ zero. | cons. k x xs ↦ zero. ] in let e : Id ℕ N m ≔ refl m in zero.
  > def f3' (m : ℕ) : ℕ ≔ let N : ℕ ≔ _ in let g : Vec ℕ N → ℕ ≔ v ↦ match v return _ [ nil. ↦ zero. | cons. k x xs ↦ zero. ] in let e : Id ℕ N m ≔ refl m in zero.
  > def f5 (m : ℕ) : ℕ ≔ let N : ℕ ≔ _ in let g : Vec ℕ (suc. N) → ℕ ≔ v ↦ match v [ cons. k x xs ↦ zero. ] in let e : Id ℕ N m ≔ refl m in zero.
  > EOF
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant Vec defined
  
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ error[E1104]
   ￭ stdin
   4 | def f2 (n : ℕ) : ℕ ≔ let A : Type ≔ _ in let g : Vec A n → ℕ ≔ v ↦ match v [ nil. ↦ zero. | cons. k x xs ↦ zero. ] in let e : Id Type A (Vec ℕ n) ≔ refl (Vec ℕ n) in zero.
     ^ this match refines the goal and context, so the parameters of its datatype
         Vec (Vec ℕ n)
       can't depend on its indices, but as placeholders were solved they turned out to.
       To match without refining, write "match … return _ [ … ]".
       If you intended a refining match, check that the placeholders were solved as you intended; giving more arguments explicitly, so that they are solved before this match or not created at all, may help.
  
   ￫ error[E1103]
   ￭ stdin
   5 | def f3 (m : ℕ) : ℕ ≔ let N : ℕ ≔ _ in let g : Vec ℕ N → ℕ ≔ v ↦ match v [ nil. ↦ zero. | cons. k x xs ↦ zero. ] in let e : Id ℕ N m ≔ refl m in zero.
     ^ can't tell whether this match can refine the goal and context, since its index
         N
       depends on unsolved placeholders.
       To match without refining, write "match … return _ [ … ]".
       If you intended a refining match, you may be able to get one by giving more arguments explicitly, so that the placeholders are solved before this match or not created at all.
  
   ￫ info[I0000]
   ￮ constant f3' defined
  
   ￫ hint[E1101]
   ￭ stdin
   7 | def f5 (m : ℕ) : ℕ ≔ let N : ℕ ≔ _ in let g : Vec ℕ (suc. N) → ℕ ≔ v ↦ match v [ cons. k x xs ↦ zero. ] in let e : Id ℕ N m ≔ refl m in zero.
     ^ match will not refine the goal or context (index is not a free variable):
         suc. N
  
   ￫ error[E1300]
   ￭ stdin
   7 | def f5 (m : ℕ) : ℕ ≔ let N : ℕ ≔ _ in let g : Vec ℕ (suc. N) → ℕ ≔ v ↦ match v [ cons. k x xs ↦ zero. ] in let e : Id ℕ N m ≔ refl m in zero.
     ^ missing match clause for constructor nil
  
  [1]

The remaining comparisons in the typechecker are postponed too.  Those that only validate something written by the user that doesn't affect the elaborated term, such as an ascribed domain of an abstraction or a supplied boundary of a constructor, are postponed without guarding anything.  The boundary of a higher-dimensional primary argument, and the bound term of a higher-dimensional let-only, are guarded by delayed metavariables.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom B : Type
  > axiom a : A
  > def ok : A ≔ let F : Type → Type ≔ _ in let h : A → A → A ≔ (x : F A) ↦ (y ↦ x) in let k : Id (Type → Type) F (X ↦ X) ≔ refl (X ↦ X) in h a a
  > def bad : A ≔ let F : Type → Type ≔ _ in let h : A → A → A ≔ (x : F B) ↦ (y ↦ x) in let k : Id (Type → Type) F (X ↦ X) ≔ refl (X ↦ X) in h a a
  > def und : A ≔ let F : Type → Type ≔ _ in let h : A → A → A ≔ (x : F A) ↦ (y ↦ x) in h a a
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > axiom n₀ : ℕ
  > axiom n₁ : ℕ
  > axiom n₂ : Id ℕ n₀ n₁
  > def cok : ℕ ≔ let F : ℕ → ℕ ≔ _ in let s : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {F zero.} {n₁} n₂ in let k : (x : ℕ) → Id ℕ (F x) n₀ ≔ x ↦ refl n₀ in zero.
  > def cbad : ℕ ≔ let F : ℕ → ℕ ≔ _ in let s : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {F zero.} {n₁} n₂ in let k : (x : ℕ) → Id ℕ (F x) n₁ ≔ x ↦ refl n₁ in zero.
  > def cund : ℕ ≔ let F : ℕ → ℕ ≔ _ in let s : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {F zero.} {n₁} n₂ in zero.
  > axiom b0 : B
  > axiom b1 : B
  > axiom b2 : Id B b0 b1
  > def lok : B ≔ let only G : Type → Type ≔ _ and x : Id (G B) ≔ b2 and k : Id (Type → Type) G (X ↦ X) ≔ refl (X ↦ X) in x.0
  > def aok : B ≔ let G : Type → Type ≔ _ in let f : G B → B ≔ _ ↦ b0 in let r ≔ refl f b2 in let k : Id (Type → Type) G (X ↦ X) ≔ refl (X ↦ X) in b0
  > def aund : B ≔ let G : Type → Type ≔ _ in let f : G B → B ≔ _ ↦ b0 in let r ≔ refl f b2 in b0
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant ok defined
  
   ￫ error[E0401]
   ￭ stdin
   5 | def bad : A ≔ let F : Type → Type ≔ _ in let h : A → A → A ≔ (x : F B) ↦ (y ↦ x) in let k : Id (Type → Type) F (X ↦ X) ≔ refl (X ↦ X) in h a a
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0406]
   ￭ stdin
   6 | def und : A ≔ let F : Type → Type ≔ _ in let h : A → A → A ≔ (x : F A) ↦ (y ↦ x) in h a a
     ^ term synthesized type
         F A
       and is being checked against type
         A
       but can't determine whether they are equal, since comparing head terms
         A
       and
         F
       depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   6 | def und : A ≔ let F : Type → Type ≔ _ in let h : A → A → A ≔ (x : F A) ↦ (y ↦ x) in h a a
     ^ can't determine a value for this placeholder
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0001]
   ￮ axiom n₀ assumed
  
   ￫ info[I0001]
   ￮ axiom n₁ assumed
  
   ￫ info[I0001]
   ￮ axiom n₂ assumed
  
   ￫ info[I0000]
   ￮ constant cok defined
  
   ￫ error[E1004]
   ￭ stdin
   12 | def cbad : ℕ ≔ let F : ℕ → ℕ ≔ _ in let s : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {F zero.} {n₁} n₂ in let k : (x : ℕ) → Id ℕ (F x) n₁ ≔ x ↦ refl n₁ in zero.
      ^ supplied 0-boundary argument
          n₁
        doesn't match the one determined by the type
          n₀
        unequal head constants:
          n₁
        does not equal
          n₀
  
   ￫ error[E1005]
   ￭ stdin
   13 | def cund : ℕ ≔ let F : ℕ → ℕ ≔ _ in let s : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {F zero.} {n₁} n₂ in zero.
      ^ can't determine whether supplied 0-boundary argument
          F 0
        matches the one determined by the type
          n₀
        since comparing head terms
          F
        and
          n₀
        depends on unsolved placeholders
  
   ￫ error[E2004]
   ￭ stdin
   13 | def cund : ℕ ≔ let F : ℕ → ℕ ≔ _ in let s : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {F zero.} {n₁} n₂ in zero.
      ^ can't determine a value for this placeholder
  
   ￫ info[I0001]
   ￮ axiom b0 assumed
  
   ￫ info[I0001]
   ￮ axiom b1 assumed
  
   ￫ info[I0001]
   ￮ axiom b2 assumed
  
   ￫ info[I0000]
   ￮ constant lok defined
  
   ￫ info[I0000]
   ￮ constant aok defined
  
   ￫ error[E0710]
   ￭ stdin
   19 | def aund : B ≔ let G : Type → Type ≔ _ in let f : G B → B ≔ _ ↦ b0 in let r ≔ refl f b2 in b0
      ^ the 0-boundary synthesized type
          B
        and is being checked against type
          G B
        but can't determine whether they are equal, since comparing head terms
          B
        and
          G
        depends on unsolved placeholders
  
   ￫ error[E0710]
   ￭ stdin
   19 | def aund : B ≔ let G : Type → Type ≔ _ in let f : G B → B ≔ _ ↦ b0 in let r ≔ refl f b2 in b0
      ^ the 1-boundary synthesized type
          B
        and is being checked against type
          G B
        but can't determine whether they are equal, since comparing head terms
          B
        and
          G
        depends on unsolved placeholders
  
   ￫ error[E0406]
   ￭ stdin
   19 | def aund : B ≔ let G : Type → Type ≔ _ in let f : G B → B ≔ _ ↦ b0 in let r ≔ refl f b2 in b0
      ^ term synthesized type
          Id B b0 b1
        and is being checked against type
          refl G (Id B) ?u13 ?u14
        but can't determine whether they are equal, since comparing head terms
          B
        and
          G
        depends on unsolved placeholders
      ^ ?u13 stands for this term, whose type hasn't been checked yet
      ^ ?u14 stands for this term, whose type hasn't been checked yet
  
   ￫ error[E2004]
   ￭ stdin
   19 | def aund : B ≔ let G : Type → Type ≔ _ in let f : G B → B ≔ _ ↦ b0 in let r ≔ refl f b2 in b0
      ^ can't determine a value for this placeholder
  
  [1]
