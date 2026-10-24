The "display let" option controls how local definitions (let-bound case trees) and holes are displayed when they appear outside their own context, i.e. with a substitution applied.

  $ cat >dl.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def sq (f : ℕ → ℕ) : ℕ → ℕ ≔ x ↦ f (f x)
  > def sqdec (x : ℕ) : ℕ ≔
  >   let dec : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ n ] in
  >   sq dec x
  > axiom z : ℕ
  > EOF

By default, they are displayed by name, with the substitution elided.

  $ narya dl.ny -e 'echo sqdec z'
  (let only … in _let.F2.0.dec) ((let only … in _let.F2.0.dec) z)
    : ℕ
  
  $ narya dl.ny -e 'display let ≔ environments' -e 'echo sqdec z'
  (let only x : ℕ ≔ z in _let.F2.0.dec)
    ((let only x : ℕ ≔ z in _let.F2.0.dec) z)
    : ℕ
  
  $ narya dl.ny -e 'display let ≔ definitions' -e 'echo sqdec z'
  (let only x : ℕ ≔ z in
   (𝑥 ↦ match #(gen) 𝑥 [ suc. n ↦ n | zero. ↦ 0 ] : ℕ → ℕ))
    ((let only x : ℕ ≔ z in
      (𝑥 ↦ match #(gen) 𝑥 [ suc. n ↦ n | zero. ↦ 0 ] : ℕ → ℕ)) z)
    : ℕ
  
  $ narya dl.ny -ascii -e 'echo sqdec z'
  (let only ... in _let.F2.0.dec) ((let only ... in _let.F2.0.dec) z)
    : ℕ
  

The option can also be cycled.

  $ narya -v -e 'display let ≔ cycle' -e 'display let ≔ cycle' -e 'display let ≔ cycle'
   ￫ info[I0101]
   ￮ display set let to environments
  
   ￫ info[I0101]
   ￮ display set let to definitions
  
   ￫ info[I0101]
   ￮ display set let to names
  

Holes have no definitions, so they are displayed by name with "definitions" too.

  $ narya dl.ny -fake-interact 'def f (x : ℕ) : ℕ ≔ sq (y ↦ y) ?  echo f z  display let ≔ environments  echo f z  display let ≔ definitions  echo f z'
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     x : ℕ
     ----------------------------------------------------------------------
     ℕ
  
  let only … in ?0
    : ℕ
  
   ￫ info[I0101]
   ￮ display set let to environments
  
  let only x : ℕ ≔ z in ?0
    : ℕ
  
   ￫ info[I0101]
   ￮ display set let to definitions
  
  let only x : ℕ ≔ z in ?0
    : ℕ
  

A recursive local definition refers to itself by name.

  $ narya -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]  def bool : Type ≔ data [ true. | false. ]' -e 'display let ≔ definitions' -e 'def ev (m : ℕ) : bool ≔ let rec even : ℕ → bool ≔ [ zero. ↦ true. | suc. n ↦ even n ] in even m' -e 'axiom k : ℕ' -e 'echo ev (suc. k)'
  (let only m : ℕ ≔ suc. k in
   (𝑥 ↦ match #(gen) 𝑥 [ suc. n ↦ _letrec.F4.0.even n | zero. ↦ true. ]
    : ℕ → bool)) k
    : bool
  

In a mutual block, the variables bound to the other local definitions are not displayed as bindings, but are referred to by name.

  $ cat >eo.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def bool : Type ≔ data [ true. | false. ]
  > def eo (m : ℕ) : bool ≔
  >   let rec even : ℕ → bool ≔ [ zero. ↦ true. | suc. n ↦ odd n ]
  >   and odd : ℕ → bool ≔ [ zero. ↦ false. | suc. n ↦ even n ] in
  >   even m
  > def eo2 : ℕ → bool ≔
  >   let rec even : ℕ → bool ≔ [ zero. ↦ true. | suc. n ↦ odd n ]
  >   and odd : ℕ → bool ≔ [ zero. ↦ false. | suc. n ↦ even n ] in
  >   odd
  > axiom k : ℕ
  > EOF

  $ narya eo.ny -e 'echo eo (suc. k)' -e 'echo eo2'
  (let only … in _letrec.F2.1.odd) k
    : bool
  
  _letrec.F2.3.odd
    : ℕ → bool
  
  $ narya eo.ny -e 'display let ≔ environments' -e 'echo eo (suc. k)' -e 'echo eo2'
  (let only m : ℕ ≔ suc. k in _letrec.F2.1.odd) k
    : bool
  
  _letrec.F2.3.odd
    : ℕ → bool
  
  $ narya eo.ny -e 'display let ≔ definitions' -e 'echo eo (suc. k)' -e 'echo eo2'
  (let only m : ℕ ≔ suc. k in
   (𝑥 ↦ match #(gen) 𝑥 [ suc. n ↦ _letrec.F2.0.even n | zero. ↦ false. ]
    : ℕ → bool)) k
    : bool
  
  𝑥 ↦ match #(gen) 𝑥 [ suc. n ↦ _letrec.F2.2.even n | zero. ↦ false. ]
    : ℕ → bool
  

Variables bound to local definitions from other blocks, such as enclosing ones, are displayed as usual.

  $ cat >nested.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def bool : Type ≔ data [ true. | false. ]
  > def h (m : ℕ) : bool ≔
  >   let rec f : ℕ → bool ≔ [ zero. ↦ true. | suc. n ↦ f n ] in
  >   let rec g : ℕ → bool ≔ [ zero. ↦ f m | suc. n ↦ g n ]
  >   and g2 : ℕ → bool ≔ [ zero. ↦ g m | suc. n ↦ g2 n ] in
  >   g2 m
  > axiom k : ℕ
  > EOF

  $ narya nested.ny -e 'display let ≔ environments' -e 'echo h k'
  (let only m : ℕ ≔ k
   and f : ℕ → bool ≔ let only m : ℕ ≔ k in _letrec.F2.0.f in
   _letrec.F2.2.g2) k
    : bool
  
  $ narya nested.ny -e 'display let ≔ definitions' -e 'echo h k'
  (let only m : ℕ ≔ k
   and f : ℕ → bool ≔
     let only m : ℕ ≔ k in
     (𝑥 ↦ match #(gen) 𝑥 [ suc. n ↦ _letrec.F2.0.f n | zero. ↦ true. ]
      : ℕ → bool) in
   (𝑥 ↦
    match #(gen) 𝑥 [ suc. n ↦ _letrec.F2.2.g2 n | zero. ↦ _letrec.F2.1.g m ]
    : ℕ → bool)) k
    : bool
  

An ascribed definition displayed as the value of a let-only clause doesn't leave its opening parenthesis alone on a line.

  $ narya -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]  axiom z : ℕ  axiom f : ℕ → ℕ → ℕ' -e 'display let ≔ definitions' -e 'def t (x : ℕ) : ℕ → ℕ ≔ let a : ℕ → ℕ ≔ let c ≔ f x x in let d : ℕ → ℕ ≔ (let e ≔ f (f x x) (f x c) in [ zero. ↦ f (f e e) (f e e) | suc. _ ↦ f (f z z) (f z z) ]) in [ zero. ↦ f (f (d z) (d z)) (d z) | suc. _ ↦ f (f z z) (f z z) ] in let b : ℕ → ℕ ≔ [ zero. ↦ a z | suc. _ ↦ z ] in b' -e 'echo t z'
  let only x : ℕ ≔ z
  and a : ℕ → ℕ ≔
    let only x : ℕ ≔ z in
    (let c ≔ f x x in
     let d ≔
       let e ≔ f (f x x) (f x c) in
       𝑥 ↦ match #(gen) 𝑥 [
       | suc. 𝑦 ↦ f (f z z) (f z z)
       | zero. ↦ f (f e e) (f e e)] in
     𝑥 ↦
     match #(gen) 𝑥 [
     | suc. 𝑦 ↦ f (f z z) (f z z)
     | zero. ↦ f (f (d z) (d z)) (d z)]
     : ℕ → ℕ) in
  (𝑥 ↦ match #(gen) 𝑥 [ suc. 𝑦 ↦ z | zero. ↦ a z ] : ℕ → ℕ)
    : ℕ → ℕ
  

The body of a let-only around a displayed definition is ascribed unless it synthesizes.  An implicitly dependent match (on a variable, refining the goal) doesn't synthesize, since its branches may have different types; but a non-dependent match synthesizes if one of its branches does, and a match with an explicit motive always synthesizes.

  $ narya -e 'def B : Type ≔ data [ true. | false. ]  def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]  def T (x : B) : Type ≔ match x [ true. ↦ B | false. ↦ ℕ ]  axiom u : B  axiom b0 : B  axiom n0 : ℕ  axiom not : B → B' -e 'def g (x : B) (b : B) (n : ℕ) : T x ≔ ((y ↦ y) : T x → T x) (match x [ true. ↦ b | false. ↦ n ])' -e 'echo g u b0 n0' -e 'def g2 (x : B) (b : B) : B ≔ ((y ↦ y) : B → B) (match not x [ true. ↦ b | false. ↦ true. ])' -e 'echo g2 u b0' -e 'def g3 (x : B) (b : B) : B ≔ ((y ↦ y) : B → B) (match x return _ ↦ B [ true. ↦ b | false. ↦ true. ])' -e 'echo g3 u b0'
  let only x : B ≔ u
  and b : B ≔ b0
  and n : ℕ ≔ n0 in
  (match #(gen) x [ false. ↦ n | true. ↦ b ] : T x)
    : T u
  
  let only x : B ≔ u
  and b : B ≔ b0 in
  match #(gen) not x [ false. ↦ true. | true. ↦ b ]
    : B
  
  let only x : B ≔ u
  and b : B ≔ b0 in
  match #(gen) x return 𝑥 ↦ B [ false. ↦ true. | true. ↦ b ]
    : B
  

The elided form can't be re-entered, but gives a helpful error message.

  $ narya dl.ny -e 'echo let only … in z'
   ￫ error[E0209]
   ￭ command-line exec string
   1 | echo let only … in z
     ^ display-only syntax can't be parsed: 'let only … in' indicates a substitution whose bindings were elided when displaying a term; to display them together with definitions instead of names, use 'display let := definitions'
  
  [1]
  $ narya dl.ny -e 'echo sq (let only ... in sq) z'
   ￫ error[E0209]
   ￭ command-line exec string
   1 | echo sq (let only ... in sq) z
     ^ display-only syntax can't be parsed: 'let only … in' indicates a substitution whose bindings were elided when displaying a term; to display them together with definitions instead of names, use 'display let := definitions'
  
  [1]

The first case-tree-only construct in a displayed definition is marked with the attribute #(gen).  When entered, it is accepted on any case tree construct, with a warning that the construct is generative.

  $ cat >gen.ny <<EOF
  > def B : Type ≔ data [ true. | false. ]
  > def f (x : B) : B ≔ match #(gen) x [ true. ↦ false. | false. ↦ true. ]
  > def f2 (x : B) : B ≔ match #(gen) x return _ ↦ B [ true. ↦ false. | false. ↦ true. ]
  > def g : B → B ≔ [ #(gen) true. ↦ false. | false. ↦ true. ]
  > def S : Type ≔ codata [ x .h : B ]
  > def s : S ≔ [ #(gen) .h ↦ true. ]
  > def E : Type ≔ data #(gen) [ ]
  > def e : E → B ≔ [ #(gen) ]
  > def R : Type ≔ sig #(gen) (a : B)
  > def C : Type ≔ codata #(gen) [ x .h : B ]
  > EOF

  $ narya -no-reformat gen.ny
   ￫ warning[W0210]
   ￭ $TESTCASE_ROOT/gen.ny
   2 | def f (x : B) : B ≔ match #(gen) x [ true. ↦ false. | false. ↦ true. ]
     ^ the attribute #(gen) indicates that this was copied from the displayed definition of a local definition or case tree; since case trees are generative, it won't be equal to the original, which may cause typechecking errors
  
   ￫ warning[W0210]
   ￭ $TESTCASE_ROOT/gen.ny
   3 | def f2 (x : B) : B ≔ match #(gen) x return _ ↦ B [ true. ↦ false. | false. ↦ true. ]
     ^ the attribute #(gen) indicates that this was copied from the displayed definition of a local definition or case tree; since case trees are generative, it won't be equal to the original, which may cause typechecking errors
  
   ￫ warning[W0210]
   ￭ $TESTCASE_ROOT/gen.ny
   4 | def g : B → B ≔ [ #(gen) true. ↦ false. | false. ↦ true. ]
     ^ the attribute #(gen) indicates that this was copied from the displayed definition of a local definition or case tree; since case trees are generative, it won't be equal to the original, which may cause typechecking errors
  
   ￫ warning[W0210]
   ￭ $TESTCASE_ROOT/gen.ny
   6 | def s : S ≔ [ #(gen) .h ↦ true. ]
     ^ the attribute #(gen) indicates that this was copied from the displayed definition of a local definition or case tree; since case trees are generative, it won't be equal to the original, which may cause typechecking errors
  
   ￫ warning[W0210]
   ￭ $TESTCASE_ROOT/gen.ny
   7 | def E : Type ≔ data #(gen) [ ]
     ^ the attribute #(gen) indicates that this was copied from the displayed definition of a local definition or case tree; since case trees are generative, it won't be equal to the original, which may cause typechecking errors
  
   ￫ warning[W0210]
   ￭ $TESTCASE_ROOT/gen.ny
   8 | def e : E → B ≔ [ #(gen) ]
     ^ the attribute #(gen) indicates that this was copied from the displayed definition of a local definition or case tree; since case trees are generative, it won't be equal to the original, which may cause typechecking errors
  
   ￫ warning[W0210]
   ￭ $TESTCASE_ROOT/gen.ny
   9 | def R : Type ≔ sig #(gen) (a : B)
     ^ the attribute #(gen) indicates that this was copied from the displayed definition of a local definition or case tree; since case trees are generative, it won't be equal to the original, which may cause typechecking errors
  
   ￫ warning[W0210]
   ￭ $TESTCASE_ROOT/gen.ny
   10 | def C : Type ≔ codata #(gen) [ x .h : B ]
      ^ the attribute #(gen) indicates that this was copied from the displayed definition of a local definition or case tree; since case trees are generative, it won't be equal to the original, which may cause typechecking errors
  

Other attributes aren't allowed on matches and comatches.

  $ narya -e 'def B : Type ≔ data [ true. | false. ]' -e 'def f (x : B) : B ≔ match #(foo) x [ true. ↦ false. | false. ↦ true. ]'
   ￫ error[E0208]
   ￭ command-line exec string
   1 | def f (x : B) : B ≔ match #(foo) x [ true. ↦ false. | false. ↦ true. ]
     ^ unrecognized attribute
  
  [1]
