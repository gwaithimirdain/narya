  $ narya -v constrs.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant twos defined
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0000]
   ￮ constant threes defined
  
   ￫ info[I0002]
   ￮ notation «_ * _ * _» defined
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant a2 defined
  
  a + a
    : twos
  
   ￫ info[I0000]
   ￮ constant a3 defined
  
  a * a * a
    : threes
  
  $ narya minus.ny
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  4
    : ℤ
  
  negsuc. 3
    : ℤ
  
  0
    : ℤ
  
  0
    : ℤ
  

  $ narya -v subminusminus.ny
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/minus.nyo
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/minus.ny (compiled)
  
   ￫ info[I0002]
   ￮ notation «_ - _» defined
  
   ￫ info[I0002]
   ￮ notation «- _» defined
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  0
    : ℤ
  
  0
    : ℤ
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/subminusminus.ny
    5 | notation(0) "-" x ≔ ℤ.minus x
      ^ previous definition
   16 | notation(0) "-" x ≔ ℤ.minus x
      ^ redefining constant: notations.«- _»
  
   ￫ warning[E2209]
   ￮ replacing printing notation for ℤ.minus (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation «- _» defined
  
  2
    : ℤ
  
   ￫ error[E0201]
   ￮ potential ambiguity (one notation is a prefix of another). Notations involved:
       «- _»
       «- _»
  
  [1]

  $ narya -v minussubminus.ny
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/minus.nyo
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/minus.ny (compiled)
  
   ￫ info[I0002]
   ￮ notation «- _» defined
  
   ￫ info[I0002]
   ￮ notation «_ - _» defined
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  0
    : ℤ
  
  0
    : ℤ
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/minussubminus.ny
    3 | notation(0) "-" x ≔ ℤ.minus x
      ^ previous definition
   16 | notation(0) "-" x ≔ ℤ.minus x
      ^ redefining constant: notations.«- _»
  
   ￫ warning[E2209]
   ￮ replacing printing notation for ℤ.minus (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation «- _» defined
  
  2
    : ℤ
  
   ￫ error[E0201]
   ￮ potential ambiguity (one notation is a prefix of another). Notations involved:
       «- _»
       «- _»
  
  [1]

  $ narya -v minusminussub.ny
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/minus.nyo
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/minus.ny (compiled)
  
   ￫ info[I0002]
   ￮ notation «- _» defined
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/minusminussub.ny
   3 | notation(0) "-" x ≔ ℤ.minus x
     ^ previous definition
   4 | notation(0) "-" x ≔ ℤ.minus x
     ^ redefining constant: notations.«- _»
  
   ￫ warning[E2209]
   ￮ replacing printing notation for ℤ.minus (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation «- _» defined
  
   ￫ info[I0002]
   ￮ notation «_ - _» defined
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
   ￫ error[E0201]
   ￮ potential ambiguity (one notation is a prefix of another). Notations involved:
       «- _»
       «- _»
  
  [1]

  $ narya negtight.ny
  b * c
    : A
  
  c
    : A
  
  a
    : A
  
  b
    : A
  
  a * b
    : A
  
  a
    : A
  

  $ narya argparens.ny
  f (- a)
    : A
  
  g (- a) b
    : A
  
  g a (- b)
    : A
  
  f a - b
    : A
  
  - a
    : A
  
  f (- - a)
    : A
  
  f (| a |)
    : A
  
  f (| - a |)
    : A
  
  f a | b
    : A
  

  $ narya bracketpostfix.ny
  a [
    : A
  
  a
    : A
  

Reformatting keeps comments inside the braces of an implicit argument in the definition of a notation.

  $ printf 'axiom A : Type\naxiom plus : {B : Type} → A → A → A\nnotation(0) x "+" y "@" B ≔ plus { {` c1 `} B {` c2 `} } x y\nnotation(0) x "⊕" y "@" B ≔ plus {\n  ` line comment\n  B} x y\n' > reformat_comments.ny
  $ narya reformat_comments.ny
   ￫ warning[E2209]
   ￮ replacing printing notation for plus (previous notation will still be parseable)
  
  $ cat reformat_comments.ny
  axiom A : Type
  
  axiom plus : {B : Type} → A → A → A
  
  notation(0) x "+" y "@" B ≔ plus { {` c1 `} B {` c2 `} } x y
  
  notation(0) x "⊕" y "@" B
    ≔ plus
        {
         ` line comment
         B} x y
  $ cp reformat_comments.ny reformat_comments_1.ny
  $ narya reformat_comments.ny
   ￫ warning[E2209]
   ￮ replacing printing notation for plus (previous notation will still be parseable)
  
  $ diff reformat_comments.ny reformat_comments_1.ny

  $ narya degenerate.ny
  x = y
    : Type
  
  x = y
    : Type
  
  p
    : x = y
  
  refl x
    : x = x
  
  n = 0
    : Type
  
  A = A
    : Type
  
  {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : 𝑥₀ = 𝑥₁) →⁽ᵉ⁾ f 𝑥₀ = f 𝑥₁
    : Type
  
  Nat⁽ᵉ⁾ 0 0
    : Type
  
  Id F p b₂
    : F x b₀ = F y b₁
  
  A⁽ᵉᵉ⁾ (refl x) (refl y) p p
    : Type
  
  A⁽ᵉᵉ⁾
    : Type⁽ᵉᵉ⁾ (Id A) (Id A) (Id A) (Id A)
  
   ￫ warning[E2209]
   ￮ replacing printing notation for refl (_ : Type) (previous notation will still be parseable)
  
  x ≡ y ∈ A
    : Type
  
  Id F p b₂
    : F x b₀ ≡ F y b₁ ∈ Type
  

The operand of a degeneracy in a notation must be ascribed to a universe, and the degenerated type must be fully instantiated by explicit arguments.

  $ narya -e 'notation(0) x "=" y ≔ Id _ x y'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: the operand of a degeneracy must be ascribed to a universe, as in (_ : Type)
  
  [1]
  $ narya -e 'notation(0) x "=" y ≔ Id x y'
   ￫ error[E0100]
   ￮ unimplemented: notations for degeneracies whose operand isn't ascribed to a universe
  
  [1]
  $ narya -e 'notation(0) x "=" y ≔ sym (_ : Type) x y'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: the degeneracy sym can't be applied to a 0-dimensional type
  
  [1]
  $ narya -e 'notation(0) x "=" y ≔ Id (_ : Typo) x y'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: not a universe: Typo
  
  [1]
  $ narya -e 'notation(0) x "=" y ≔ Id (_ : Type) x {y}'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: the arguments instantiating a degenerated type must be explicit
  
  [1]
  $ narya -e 'notation(0) "Eq" x ≔ Id (_ : Type) x'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: a degenerated type must be instantiated by 2 arguments
  
  [1]
  $ narya -e 'notation(0) "Eq" ≔ Id'
   ￫ error[E0600]
   ￮ missing argument for degeneracy Id
  
  [1]
  $ narya -e 'axiom g : Type → Type → Type → Type' -e 'notation(0) x "=" y ≔ g (_ : Type) x y'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: only the operand of a degeneracy can be ascribed to a universe
  
  [1]
  $ narya -e 'notation(0) x "=" y ≔ Id (_ : Type) x y' -e 'def Nat : Type ≔ data [ zero. | suc. (n : Nat) ]' -e 'def f (n : Nat) : Nat ≔ match n [ x = y ↦ zero. | _ ↦ zero. ]'
   ￫ error[E2202]
   ￭ command-line exec string
   1 | def f (n : Nat) : Nat ≔ match n [ x = y ↦ zero. | _ ↦ zero. ]
     ^ invalid notation pattern: «_ = _»
  
  [1]

Other arities.

  $ narya -parametric -direction p,rel,Br -arity 3 -e 'axiom A : Type' -e 'axiom x : A' -e 'notation(0) x "≡" y "≡" z ≔ Br (_ : Type) x y z' -e 'echo Br A x x x'
  x ≡ x ≡ x
    : Type
  
  $ narya -parametric -direction p,rel,Br -arity 1 -e 'axiom A : Type' -e 'axiom x : A' -e 'notation(0) "D" x ≔ Br (_ : Type) x' -e 'echo Br A x' -e 'echo rel x'
  D x
    : Type
  
  rel x
    : D x
  
  $ narya -parametric -direction p,rel,Br -arity 0 -e 'axiom A : Type' -e 'axiom a : A' -e 'notation(0) "Z" A ≔ Br (A : Type) .' -e 'echo Br A .' -e 'echo rel a' -e 'echo Br Type .'
  Z A
    : Type
  
  rel a
    : Z A
  
  Z Type
    : Type
  

In arity 0 the dot of the nullary instantiation must be written, since without it the notation would mean an uninstantiated 1-dimensional type.  A dot is allowed nowhere else.

  $ narya -parametric -direction p,rel,Br -arity 0 -e 'notation(0) "Z" A ≔ Br (A : Type)'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: in arity 0, a degenerated type must be instantiated by a single "."
  
  [1]
  $ narya -e 'notation(0) x "=" y ≔ Id (_ : Type) x .'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: a dot is allowed only to instantiate a degenerated type in arity 0
  
  [1]
  $ narya -e 'axiom g : Type → Type' -e 'notation(0) "G" ≔ g .'
   ￫ error[E2210]
   ￮ invalid arguments of notation head: a dot is allowed only to instantiate a degenerated type in arity 0
  
  [1]

A notation for a degeneracy of a type applies only in the mode of the universe its operand is ascribed to, including behind locks.  Notations in different modes don't replace each other.

  $ narya -composable-functors -e 'def ▱○ (X :▱○| AType) : CType ≔ data [ ▱○. (_ :▱○| X) ]' -e 'notation(0) x "=" y ≔ Id (_ : CType) x y' -e 'axiom T : (X :▱○| AType) (x y :▱○| X) (C : CType) (c : C) → ▱○ (Id X x y) → Id C c c' -e 'echo T' -e 'notation(0) x "≡" y ≔ Id (_ : AType) x y' -e 'echo T' -e 'axiom T′ : (X :▱○| AType) (x y :▱○| X) → ▱○ (x = y)'
  T
    : (X :▱○| AType) (x :▱○| X) (y :▱○| X) (C : CType) (c : C) →
      ▱○ (Id X x y)
      → c = c
  
  T
    : (X :▱○| AType) (x :▱○| X) (y :▱○| X) (C : CType) (c : C) → ▱○ (x ≡ y)
      → c = c
  
   ￫ error[E1700]
   ￭ command-line exec string
   1 | axiom T′ : (X :▱○| AType) (x y :▱○| X) → ▱○ (x = y)
     ^ mode mismatch in synthesizing universe (CType ≠ AType)
  
  [1]

Reformatting.

  $ printf 'notation(0) x "=" y ≔ Id (  _   :Type  ) x y\n' > reformat_deg.ny
  $ narya reformat_deg.ny
  $ cat reformat_deg.ny
  notation(0) x "=" y ≔ Id (_ : Type) x y
  $ printf 'notation(0) "Z" ≔ Br (  _   :Type  )   .\n' > reformat_deg0.ny
  $ narya -parametric -direction p,rel,Br -arity 0 reformat_deg0.ny
  $ cat reformat_deg0.ny
  notation "Z" ≔ Br (_ : Type) .
  $ printf 'notation(0) x "=" y ≔ Id ( {` c3 `} _ {` c4 `} : {` c5 `} Type {` c6 `} ) x y\nnotation(0) x "≡" y ≔ Id (\n  ` line comment\n  _ : Type) x y\n' > reformat_deg_comments.ny
  $ narya reformat_deg_comments.ny
   ￫ warning[E2209]
   ￮ replacing printing notation for Id (_ : Type) (previous notation will still be parseable)
  
  $ cat reformat_deg_comments.ny
  notation(0) x "=" y
    ≔ Id ( {` c3 `} _ {` c4 `} : {` c5 `} Type {` c6 `} ) x y
  
  notation(0) x "≡" y
    ≔ Id
        (
         ` line comment
         _ : Type) x y
  $ cp reformat_deg_comments.ny reformat_deg_comments_1.ny
  $ narya reformat_deg_comments.ny
   ￫ warning[E2209]
   ￮ replacing printing notation for Id (_ : Type) (previous notation will still be parseable)
  
  $ diff reformat_deg_comments.ny reformat_deg_comments_1.ny
