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
  
   ￫ error[E0401]
   ￭ stdin
   11 | def scoped : A → Type ≔ let f : (w : A) → Type ≔ _ in x ↦ let g : (w : A) → Type ≔ _ in let k : Id Type (f x) (g x) ≔ refl (g x) in A
      ^ term synthesized type
          Type⁽ᵉ⁾ (g x) (g x)
        but is being checked against type
          Type⁽ᵉ⁾ (f x) (g x)
        unequal head metavariables:
          ?u5
        does not equal
          ?u4
  
  [1]

Eta-contraction doesn't change the problem: ?f x x =? h x uses a repeated variable, even though ?f x =? h wouldn't.

  $ narya - <<EOF
  > axiom A : Type
  > axiom h : A → Type
  > def repeated : Type ≔ let f : A → A → Type ≔ _ in let k : (x : A) → Id Type (f x x) (h x) ≔ x ↦ refl (h x) in A
  > EOF
   ￫ error[E0401]
   ￭ stdin
   3 | def repeated : Type ≔ let f : A → A → Type ≔ _ in let k : (x : A) → Id Type (f x x) (h x) ≔ x ↦ refl (h x) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (h x) (h x)
       but is being checked against type
         Type⁽ᵉ⁾ (f x x) (h x)
       unequal head terms:
         h
       does not equal
         f
  
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
   ￫ error[E0401]
   ￭ stdin
   4 | def envarg : A → Type ≔ x ↦ let f : A → Type ≔ _ in let k : Id Type (f x) (B x) ≔ refl (B x) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B x) (B x)
       but is being checked against type
         Type⁽ᵉ⁾ (f x) (B x)
       unequal head terms:
         B
       does not equal
         f
  
   ￫ error[E0401]
   ￭ stdin
   5 | def reparg : Type ≔ let f : A → A → Type ≔ _ in let k : (y : A) → Id Type (f y y) (B y) ≔ y ↦ refl (B y) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B y) (B y)
       but is being checked against type
         Type⁽ᵉ⁾ (f y y) (B y)
       unequal head terms:
         B
       does not equal
         f
  
   ￫ error[E0401]
   ￭ stdin
   6 | def nonvar : Type ≔ let f : A → Type ≔ _ in let k : Id Type (f a0) (B a0) ≔ refl (B a0) in A
     ^ term synthesized type
         Type⁽ᵉ⁾ (B a0) (B a0)
       but is being checked against type
         Type⁽ᵉ⁾ (f a0) (B a0)
       unequal head terms:
         B
       does not equal
         f
  
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
  
   ￫ error[E0401]
   ￭ stdin
   9 | def tydep : (Z : Type) → Type ≔ let m : (X Y : Type) → X → Y → Y ≔ _ in Z ↦ let k : Id (Z → Z → Z) (m Z Z) ((x y ↦ y) : Z → Z → Z) ≔ refl ((x y ↦ y) : Z → Z → Z) in Z
     ^ term synthesized type
         {𝑥₀ : Z} {𝑥₁ : Z} (𝑥₂ : Id Z 𝑥₀ 𝑥₁) {𝑦₀ : Z} {𝑦₁ : Z} (𝑦₂ : Id Z 𝑦₀ 𝑦₁)
         →⁽ᵉ⁾ Id Z 𝑦₀ 𝑦₁
       but is being checked against type
         {𝑥₀ : Z} {𝑥₁ : Z} (𝑥₂ : Id Z 𝑥₀ 𝑥₁) {𝑦₀ : Z} {𝑦₁ : Z} (𝑦₂ : Id Z 𝑦₀ 𝑦₁)
         →⁽ᵉ⁾ Id Z (m Z Z 𝑥₀ 𝑦₀) 𝑦₁
       unequal head terms:
         𝑦
       does not equal
         m
  
   ￫ error[E0401]
   ￭ stdin
   10 | def vardep : (Z : Type) (z : Z) (e : Z → Type) → Type ≔ let G : (X Y : Type) (c : X) (e : Y → Type) → Type ≔ _ in Z z e ↦ let k : Id Type (G Z Z z e) (e z) ≔ refl (e z) in Type
      ^ term synthesized type
          Type⁽ᵉ⁾ (e z) (e z)
        but is being checked against type
          Type⁽ᵉ⁾ (G Z Z z e) (e z)
        unequal head terms:
          e
        does not equal
          G
  
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
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E0401]
   ￭ stdin
   6 | def stream : A ≔ let s : S ≔ _ in let k : Id A (s .head) a0 ≔ refl a0 in a0
     ^ term synthesized type
         Id A a0 a0
       but is being checked against type
         Id A (s .head) a0
       unequal head terms:
         a0
       does not equal
         s
  
   ￫ error[E0401]
   ￭ stdin
   7 | def samem : A ≔ let p : Pr ≔ _ in let k : Id A (p .fst) (p .snd) ≔ refl (p .snd) in a0
     ^ term synthesized type
         Id A (p .snd) (p .snd)
       but is being checked against type
         Id A (p .fst) (p .snd)
       unequal fields:
         snd
       does not equal
         fst
  
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
  
   ￫ error[E0401]
   ￭ stdin
   12 | def varrhs (z :△□| C) : C ≔ let r :△| □′ C ≔ _ in let k : Id C ((r :△| _) .□) z ≔ refl z in (r :△| _) .□
      ^ term synthesized type
          Id C z z
        but is being checked against type
          Id C ?u8 z
        unequal head terms:
          z
        does not equal
          ?u8
  
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
   ￮ there is 1 unsolved unification metavariable
  
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
   ￫ error[E0401]
   ￭ stdin
   5 | def stuck : A ≔ let c : Bool ≔ _ in let x : A ≔ _ in let k : Id A (st c x) (st c a1) ≔ refl (st c a1) in a1
     ^ term synthesized type
         Id A (st c a1) (st c a1)
       but is being checked against type
         Id A (st c x) (st c a1)
       unequal head terms:
         a1
       does not equal
         x
  
   ￫ error[E0401]
   ￭ stdin
   6 | def head : A ≔ let m : A → A ≔ _ in let x : A ≔ _ in let k : Id A (m x) (m a1) ≔ refl (m a1) in a1
     ^ term synthesized type
         Id A (m a1) (m a1)
       but is being checked against type
         Id A (m x) (m a1)
       unequal head terms:
         a1
       does not equal
         x
  
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
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there are 2 unsolved unification metavariables
  
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
