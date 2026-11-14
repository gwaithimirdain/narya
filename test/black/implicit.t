Implicit function-types are written with braces around their domains, as are their abstraction variables and their arguments when given explicitly.  They are never equal to explicit function-types.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom a : A
  > axiom f : {x : A} → B x
  > def t : B a ≔ f {a}
  > echo f {a}
  > synth {_ : A} → B a
  > def g : {x : A} → B x ≔ {x} ↦ f {x}
  > echo ({y} ↦ f {y}) : {x : A} → B x
  > echo ({x : A} ↦ f {x})
  > def F : {x : A} (y : B x) {z : A} → Type ≔ {x} y {z} ↦ B z
  > synth F
  > def id : {X : Type} (x : X) → X ≔ {X} x ↦ x
  > echo id {A} a
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant t defined
  
  f .
    : B a
  
  {𝑥 : A} → B a
    : Type
  
   ￫ info[I0000]
   ￮ constant g defined
  
  {y} ↦ f .
    : {x : A} → B x
  
  {x} ↦ f .
    : {x : A} → B x
  
   ￫ info[I0000]
   ￮ constant F defined
  
  F
    : {x : A} (y : B x) {z : A} → Type
  
   ￫ info[I0000]
   ￮ constant id defined
  
  a
    : A
  

Abstractions and arguments must be implicit exactly when their function-type is, and an implicit function-type is not equal to an explicit one.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom a : A
  > axiom f : {x : A} → B x
  > axiom fe : (x : A) → B x
  > def h1 : {x : A} → B x ≔ x ↦ f {x}
  > def h2 : (x : A) → B x ≔ {x} ↦ f {x}
  > def h3 : B a ≔ fe {a}
  > def h4 : (x : A) → B x ≔ f
  > def h5 : {x : A} → B x ≔ fe
  > EOF
   ￫ error[E0702]
   ￭ stdin
   6 | def h1 : {x : A} → B x ≔ x ↦ f {x}
     ^ unexpected explicit abstraction: the function-type is implicit, so its variable must be in braces
  
   ￫ error[E0702]
   ￭ stdin
   7 | def h2 : (x : A) → B x ≔ {x} ↦ f {x}
     ^ unexpected implicit abstraction: expecting explicit variable
  
   ￫ error[E0702]
   ￭ stdin
   8 | def h3 : B a ≔ fe {a}
     ^ unexpected implicit argument: the function-type is explicit
  
   ￫ error[E0401]
   ￭ stdin
   9 | def h4 : (x : A) → B x ≔ f
     ^ term synthesized type
         {x : A} → B x
       but is being checked against type
         (x : A) → B x
       unequal head terms:
         {x : A} → B x
       does not equal
         (x : A) → B x
  
   ￫ error[E0401]
   ￭ stdin
   10 | def h5 : {x : A} → B x ≔ fe
      ^ term synthesized type
          (x : A) → B x
        but is being checked against type
          {x : A} → B x
        unequal head terms:
          (x : A) → B x
        does not equal
          {x : A} → B x
  
  [1]

Implicit arguments are displayed only if requested, in which case a notation isn't used for an application with implicit arguments.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom a : A
  > axiom f : {x : A} → B x
  > axiom g : {x : A} (y : B x) → B x
  > notation(1) y "!" ≔ g y
  > echo g {a} (f {a})
  > echo (y ↦ g {a} y) : B a → B a
  > display implicits ≔ on
  > echo g {a} (f {a})
  > echo (y ↦ g {a} y) : B a → B a
  > echo ({y} ↦ f {y}) : {x : A} → B x
  > EOF
  f . !
    : B a
  
  y ↦ y !
    : B a → B a
  
  g {a} (f {a})
    : B a
  
  y ↦ g {a} y
    : B a → B a
  
  {y} ↦ f {y}
    : {x : A} → B x
  

Implicit function-types can be modal.

  $ narya -spatial - <<EOF
  > axiom A : Type
  > axiom B : Type
  > axiom f : {x :♭| A} → B
  > axiom a : A
  > synth f
  > def g : {x :♭| A} → B ≔ {x} ↦ f {x}
  > def r (z :♭| A) : B ≔ f {z}
  > def s (z : A) : B ≔ f {z}
  > EOF
  f
    : {x :♭| A} → B
  
   ￫ error[E1705]
   ￭ stdin
   8 | def s (z : A) : B ≔ f {z}
     ^ use of id variable behind ♭ lock requires a key
  
  [1]

The identity type of an implicit function-type is an implicit higher-dimensional function-type, all of whose arguments are implicit.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom f : {x : A} → B x
  > axiom a : A
  > synth refl f
  > echo refl f {a} {a} {refl a}
  > def r : Id ({x : A} → B x) f f ≔ {x₀} {x₁} {x₂} ↦ refl f {x₀} {x₁} {x₂}
  > def r2 : Id ({x : A} → B x) f f ≔ {x} ⤇ refl f {x.0} {x.1} {x.2}
  > def r3 : Id ({x : A} → B x) f f ≔ x ⤇ refl f {x.0} {x.1} {x.2}
  > def r4 : Id ({x : A} → B x) f f ≔ {x₀} {x₁} x₂ ↦ refl f {x₀} {x₁} {x₂}
  > echo refl f {a} {a} (refl a)
  > display implicits ≔ on
  > synth refl f
  > EOF
  ap f
    : {x₀ : A} {x₁ : A} {x₂ : Id A x₀ x₁} →⁽ᵉ⁾ Id B x₂ (f .) (f .)
  
  ap f .
    : Id B (refl a) (f .) (f .)
  
   ￫ error[E0702]
   ￭ stdin
   9 | def r3 : Id ({x : A} → B x) f f ≔ x ⤇ refl f {x.0} {x.1} {x.2}
     ^ unexpected explicit cube abstraction: the function-type is implicit, so its variable must be in braces
  
   ￫ error[E0702]
   ￭ stdin
   10 | def r4 : Id ({x : A} → B x) f f ≔ {x₀} {x₁} x₂ ↦ refl f {x₀} {x₁} {x₂}
      ^ unexpected explicit abstraction: the function-type is implicit, so its variable must be in braces
  
   ￫ error[E0702]
   ￭ stdin
   11 | echo refl f {a} {a} (refl a)
      ^ unexpected explicit argument: the function-type is implicit, so its argument must be in braces
  
  ap f
    : {x₀ : A} {x₁ : A} {x₂ : Id A x₀ x₁}
      →⁽ᵉ⁾ Id B {x₀} {x₁} x₂ (f {x₀}) (f {x₁})
  
  [1]

In a matching abstraction, a top-level pattern in braces makes the abstraction over the variable it matches implicit.  All the branches must agree.

  $ narya - <<EOF
  > def Nat : Type ≔ data [ zero. | suc. (_ : Nat) ]
  > def p : {_ : Nat} → Nat ≔ [ {zero.} ↦ zero. | {suc. n} ↦ n ]
  > echo p {3}
  > def q : {_ : Nat} (_ : Nat) → Nat ≔ [ {zero.}, m ↦ m | {suc. n}, _ ↦ n ]
  > about q
  > def v : {_ : Nat} → Nat ≔ [ {n} ↦ n ]
  > def b1 : {_ : Nat} → Nat ≔ [ {zero.} ↦ zero. | suc. n ↦ n ]
  > def b2 : {_ : Nat} → Nat ≔ [ zero. ↦ zero. | suc. n ↦ n ]
  > def b3 : Nat → Nat ≔ [ {zero.} ↦ zero. | {suc. n} ↦ n ]
  > EOF
  2
    : Nat
  
  {𝑥} 𝑦 ↦ match 𝑥 [ suc. n ↦ n | zero. ↦ 𝑦 ]
    : {𝑥 : Nat} → Nat → Nat
  
   ￫ error[E0702]
   ￭ stdin
   7 | def b1 : {_ : Nat} → Nat ≔ [ {zero.} ↦ zero. | suc. n ↦ n ]
     ^ unexpected explicit pattern: all the branches of a matching abstraction must have the same patterns in braces
  
   ￫ error[E0702]
   ￭ stdin
   8 | def b2 : {_ : Nat} → Nat ≔ [ zero. ↦ zero. | suc. n ↦ n ]
     ^ unexpected explicit abstraction: the function-type is implicit, so its variable must be in braces
  
   ￫ error[E0702]
   ￭ stdin
   9 | def b3 : Nat → Nat ≔ [ {zero.} ↦ zero. | {suc. n} ↦ n ]
     ^ unexpected implicit abstraction: expecting explicit variable
  
  [1]

Applying an implicit function to an explicit argument inserts placeholders for its leading implicit arguments.  A dot inserts one (cube of) implicit argument, and an ellipsis inserts all the leading ones.  They are also inserted before a field projection.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom a : A
  > axiom b : B a
  > axiom f : {x : A} → B x
  > axiom g : {x : A} (y : B x) → B x
  > def t1 : B a ≔ g b
  > echo g b
  > def t2 : B a ≔ f .
  > def t3 : B a ≔ f …
  > def id : {X : Type} (x : X) → X ≔ {X} x ↦ x
  > echo id b
  > axiom h : {x : A} {y : B x} (z : A) → A
  > def t4 : A ≔ h {a} {b} a
  > def t5 : A ≔ h . {b} a
  > def t6 (y : B a) : A ≔ h . {y} a
  > def R : Type ≔ sig ( fst : A, snd : A )
  > axiom r : {x : A} {y : B x} → R
  > def t7 : A ≔ (r {a} {b}) .fst
  > EOF
  g b
    : B a
  
  b
    : B a
  

Implicit arguments that can't be determined are reported.  A term of implicit function-type isn't applied to its implicit arguments automatically if it isn't applied to anything, so checking it against a type that isn't a function-type suggests inserting them.

  $ narya - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom a : A
  > axiom b : B a
  > axiom f : {x : A} → B x
  > axiom h : {x : A} {y : B x} (z : A) → A
  > echo h a
  > echo h . . a
  > def R : Type ≔ sig ( fst : A, snd : A )
  > axiom r : {x : A} → R
  > echo r .fst
  > def t : B a ≔ f
  > echo b …
  > EOF
   ￫ error[E2005]
   ￭ stdin
   7 | echo h a
     ^ can't determine implicit argument x of h
  
   ￫ error[E2005]
   ￭ stdin
   8 | echo h . . a
     ^ can't determine implicit argument x of h
  
   ￫ error[E2005]
   ￭ stdin
   8 | echo h . . a
     ^ can't determine implicit argument y of h
  
   ￫ error[E2005]
   ￭ stdin
   11 | echo r .fst
      ^ can't determine implicit argument x of r
  
   ￫ error[E0401]
   ￭ stdin
   12 | def t : B a ≔ f
      ^ term synthesized type
          {x : A} → B x
        but is being checked against type
          B a
        unequal head terms:
          {x : A} → B x
        does not equal
          B
   ￮ the term has an implicit function-type: to insert its implicit arguments, apply it to "." or "…"
  
   ￫ error[E0711]
   ￭ stdin
   13 | echo b …
      ^ nothing to insert or instantiate: ellipsis applied to a term whose type is neither an implicit function-type nor a higher-dimensional type of arity zero
  
  [1]

Notations insert implicit arguments in the same way, and are used for display when implicit arguments are hidden.

  $ narya - <<EOF
  > def List (A : Type) : Type ≔ data [ nil. | cons. (_ : A) (_ : List A) ]
  > def append : {A : Type} (xs ys : List A) → List A
  >   ≔ {A} xs ys ↦ match xs [ nil. ↦ ys | cons. x xs ↦ cons. x (append xs ys) ]
  > notation(3) xs "++" ys ≔ append xs ys
  > def l2 (A : Type) (xs : List A) : List A ≔ xs ++ xs
  > about l2
  > display implicits ≔ on
  > about l2
  > EOF
  A xs ↦ xs ++ xs
    : (A : Type) (xs : List A) → List A
  
  A xs ↦ append {A} xs xs
    : (A : Type) (xs : List A) → List A
  

In arity zero, an ellipsis also instantiates all the leading nullary dimensions of a type, but it doesn't do both kinds of steps at once.

  $ narya -parametric -arity 0 -direction w,wk - <<EOF
  > axiom A : Type
  > axiom a : A
  > axiom T : {x : A} → Type
  > echo wk (wk A) …
  > echo wk (wk A) . …
  > synth wk (wk T) {wk (wk a)} …
  > synth wk (wk T) {wk (wk a)} . .
  > synth wk (wk T) {wk (wk a)} … …
  > echo wk (wk A) . . …
  > EOF
  A⁽ʷʷ⁾ . .
    : Type
  
  A⁽ʷʷ⁾ . .
    : Type
  
  wk (wk T) . . .
    : Type
  
  wk (wk T) . . .
    : Type
  
   ￫ error[E0711]
   ￭ stdin
   8 | synth wk (wk T) {wk (wk a)} … …
     ^ nothing to insert or instantiate: ellipsis applied to a term whose type is neither an implicit function-type nor a higher-dimensional type of arity zero
  
   ￫ error[E0711]
   ￭ stdin
   9 | echo wk (wk A) . . …
     ^ nothing to insert or instantiate: ellipsis applied to a term whose type is neither an implicit function-type nor a higher-dimensional type of arity zero
  
  [1]

With implicit arguments hidden, a hidden cube of them is displayed as a dot, so that the display re-parses, unless it would be inserted anyway because it is followed by an explicit argument or a field projection.

  $ narya - <<EOF
  > axiom A : Type
  > axiom a : A
  > axiom B : A → Type
  > axiom b : B a
  > def R : Type ≔ sig ( fst : A, snd : A )
  > axiom r : {x : A} {y : B x} → R
  > axiom g : {x : A} (y : B x) → B x
  > echo r {a} {b}
  > echo (r {a} {b}) .snd
  > echo g {a} b
  > EOF
  r . .
    : R
  
  r .snd
    : A
  
  g b
    : B a
  

Parameters of definitions and axioms in braces make the corresponding arguments of the constant implicit.

  $ narya -spatial - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom a : A
  > axiom b : B a
  > def id {X : Type} (x : X) : X ≔ x
  > echo id b
  > synth id
  > about id
  > axiom f {x : A} (y : B x) : B x
  > echo f b
  > def g {x y : A} (z : B y) : B y ≔ z
  > synth g
  > def s {X : Type} ≔ (x : X) ↦ x
  > synth s
  > def h {x :♭| A} : A ≔ a
  > synth h
  > def List {A : Type} : Type ≔ data [ nil. | cons. (_ : A) (_ : List {A}) ]
  > def len {X : Type} : List {X} → Type ≔ [ nil. ↦ A | cons. _ xs ↦ len xs ]
  > def l : List {A} ≔ cons. a nil.
  > echo len l
  > EOF
  b
    : B a
  
  id
    : {X : Type} (x : X) → X
  
  {X} x ↦ x
    : {X : Type} (x : X) → X
  
  f b
    : B a
  
  g
    : {x : A} {y : A} (z : B y) → B y
  
  s
    : {X : Type} (x : X) → X
  
  h
    : {x :♭| A} → A
  
  A
    : Type
  

Braces in parameters are preserved by reformatting.

  $ cat >rf.ny <<EOF
  > axiom A : Type
  > def id   {X:Type} (x : X) : X ≔ x
  > axiom f {x y : A} (z :  A) : A
  > EOF
  $ narya rf.ny
  $ cat rf.ny
  axiom A : Type
  
  def id {X : Type} (x : X) : X ≔ x
  
  axiom f {x y : A} (z : A) : A
