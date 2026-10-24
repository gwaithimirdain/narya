Testing let-bindings

  $ cat >pre.ny <<EOF
  > axiom A:Type
  > axiom a0:A
  > axiom a1:A
  > axiom a2: Id A a0 a1
  > axiom B : A → Type
  > axiom b : B a0
  > axiom f : (x:A) → B x → B x
  > EOF

  $ narya -source-only -v pre.ny -e "def a0' : A := let id ≔ ((x ↦ x) : A → A) in id a0" -e "def test : Id A a0 a0' := refl a0"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant a0' defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

  $ narya -source-only -v pre.ny -e "def a0' : A := let id : A → A ≔ x ↦ x in id a0" -e "def test : Id A a0 a0' := refl a0"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant a0' defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

It matters what the variable is bound to:

  $ narya -source-only -v pre.ny -e "def a0' : A := let id : A → A ≔ x ↦ a1 in id a0" -e "def untest : Id A a0 a0' := refl a0"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant a0' defined
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def untest : Id A a0 a0' := refl a0
     ^ term synthesized type
         Id A a0 a0
       but is being checked against type
         Id A a0 a1
       unequal head constants:
         a0
       does not equal
         a1
  
  [1]

Ap on let:

  $ narya -source-only -v pre.ny -e "def a2' := refl ((y ↦ let id : A → A ≔ x ↦ x in id y) : A → A) a2" -e "def test : Id (Id A a0 a1) a2 a2' := refl a2"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant a2' defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

Let affects typechecking:

  $ narya -source-only -v pre.ny -e "def b' : B a0 := let x ≔ a0 in f x b" -e "def untest : B a0 ≔ ((x ↦ f x b) : A → B a0) a0"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant b' defined
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def untest : B a0 ≔ ((x ↦ f x b) : A → B a0) a0
     ^ term synthesized type
         B a0
       but is being checked against type
         B x
       unequal head terms:
         a0
       does not equal
         x
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def untest : B a0 ≔ ((x ↦ f x b) : A → B a0) a0
     ^ term synthesized type
         B x
       but is being checked against type
         B a0
       unequal head terms:
         x
       does not equal
         a0
  
  [1]

Let can check in addition to synthesize:

  $ narya -source-only -v pre.ny -e "def aconst : A → A ≔ let x ≔ a0 in y ↦ x"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant aconst defined
  

Let is allowed in case trees:

  $ narya -source-only -v pre.ny -e "def atree : A → A ≔ let x ≔ a0 in y ↦ y" -e "echo atree"
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant atree defined
  
  atree
    : A → A
  

Let can contain case trees:

  $ cat >letcase.ny <<EOF
  > def bool : Type := data [ true. | false. ]
  > axiom u : bool
  > EOF

  $ narya -source-only -v letcase.ny -e 'def not : bool -> bool := x |-> let n : bool := match x [ true. |-> false. | false. |-> true. ] in n' -e 'echo not true.' -e 'echo not false.' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ axiom u assumed
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false.
    : bool
  
  true.
    : bool
  
  let only … in _let.F3.0.n
    : bool
  

  $ narya -source-only -v letcase.ny -e 'def not : bool -> bool := x |-> let n : bool -> bool := y |-> match y [ true. |-> false. | false. |-> true. ] in n x' -e 'echo not true.' -e 'echo not false.' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ axiom u assumed
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false.
    : bool
  
  true.
    : bool
  
  (let only … in _let.F3.0.n) u
    : bool
  

Synthesizing matches don't need to be annotated

  $ narya -source-only -v letcase.ny -e 'def not : bool -> bool := x |-> let n := match x [ true. |-> (false. : bool) | false. |-> true. ] in n' -e 'echo not true.' -e 'echo not false.' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ axiom u assumed
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def not : bool -> bool := x |-> let n := match x [ true. |-> (false. : bool) | false. |-> true. ] in n
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false.
    : bool
  
  true.
    : bool
  
  let only … in _let.F3.0.n
    : bool
  

Either branch can synthesize:

  $ narya -source-only -v letcase.ny -e 'def not : bool -> bool := x |-> let n := match x [ true. |-> false. | false. |-> (true. : bool) ] in n' -e 'echo not true.' -e 'echo not false.' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ axiom u assumed
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def not : bool -> bool := x |-> let n := match x [ true. |-> false. | false. |-> (true. : bool) ] in n
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false.
    : bool
  
  true.
    : bool
  
  let only … in _let.F3.0.n
    : bool
  

Let doesn't make a case tree unless it needs to:

  $ cat >letnocase.ny <<EOF
  > def prod (A B : Type) : Type := sig (fst : A, snd : B)
  > def foo : prod (Type -> Type) Type := ( fst := X |-> X, snd := Type )
  > echo foo
  > def foo' : prod (Type -> Type) Type := let z : prod (Type -> Type) Type := ( fst := X |-> X, snd := Type ) in z
  > echo foo'
  > EOF

  $ narya -v letnocase.ny
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant foo defined
  
  foo
    : prod (Type → Type) Type
  
   ￫ info[I0000]
   ￮ constant foo' defined
  
  (fst ≔ X ↦ X, snd ≔ Type)
    : prod (Type → Type) Type
  

Matches outside case trees can be implicitly wrapped in a let-binding:

  $ narya -source-only -v letcase.ny -e 'def not (b : bool) : bool ≔ ((x ↦ x) : bool → bool) (match b [ true. ↦ false. | false. ↦ true. ])' -e 'echo not true.' -e 'echo not false.' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ axiom u assumed
  
   ￫ hint[H0403]
   ￭ command-line exec string
   1 | def not (b : bool) : bool ≔ ((x ↦ x) : bool → bool) (match b [ true. ↦ false. | false. ↦ true. ])
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false.
    : bool
  
  true.
    : bool
  
  let only b : bool ≔ u in
  (match b [ false. ↦ true. | true. ↦ false. ] : bool)
    : bool
  

Pattern-matching lambdas can be used in arbitrary places:

  $ narya -v - <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
  > def square (f : ℕ → ℕ) : ℕ → ℕ ≔ x ↦ f (f x)
  > def squaredec : ℕ → ℕ ≔ square [ zero. ↦ zero. | suc. n ↦ n ]
  > echo squaredec 4
  > echo squaredec 1
  > axiom n : ℕ
  > echo squaredec n
  > EOF
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant square defined
  
   ￫ hint[H0403]
   ￭ stdin
   3 | def squaredec : ℕ → ℕ ≔ square [ zero. ↦ zero. | suc. n ↦ n ]
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant squaredec defined
  
  2
    : ℕ
  
  0
    : ℕ
  
   ￫ info[I0001]
   ￮ axiom n assumed
  
  let only 𝑥 : ℕ ≔
    let only 𝑥 : ℕ ≔ n in
    (match 𝑥 [ suc. n ↦ n | zero. ↦ 0 ] : ℕ) in
  (match 𝑥 [ suc. n ↦ n | zero. ↦ 0 ] : ℕ)
    : ℕ
  

Matches in definitions of datatypes

  $ narya -v - <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def Foo (b : Bool) : Type ≔ data [ foo. (_ : match b [ true. ↦ Bool | false. ↦ Bool ]) ]
  > def f : Foo true. ≔ foo. false.
  > EOF
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ hint[H0403]
   ￭ stdin
   2 | def Foo (b : Bool) : Type ≔ data [ foo. (_ : match b [ true. ↦ Bool | false. ↦ Bool ]) ]
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant Foo defined
  
   ￫ info[I0000]
   ￮ constant f defined
  

Matches in non-toplevel definitions of datatype

  $ narya -v - <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def prod (A B : Type) : Type ≔ sig (fst : A, snd : B)
  > def Foo (b : Bool) : Type ≔ prod Bool (data [ foo. (_ : match b [ true. ↦ Bool | false. ↦ Bool ]) ])
  > def f : Foo true. ≔ (true., foo. false.)
  > EOF
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ hint[H0403]
   ￭ stdin
   3 | def Foo (b : Bool) : Type ≔ prod Bool (data [ foo. (_ : match b [ true. ↦ Bool | false. ↦ Bool ]) ])
     ^ data encountered outside case tree, wrapping in implicit let-binding
  
   ￫ hint[H0403]
   ￭ stdin
   3 | def Foo (b : Bool) : Type ≔ prod Bool (data [ foo. (_ : match b [ true. ↦ Bool | false. ↦ Bool ]) ])
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant Foo defined
  
   ￫ info[I0000]
   ￮ constant f defined
  


In a hole, a let-bound variable whose value is its metavariable is displayed as that variable, including in the values of later let-bound variables.

  $ narya -v letcase.ny -e 'def J (A : Type) (a : A) : A → Type ≔ data [ rfl. : J A a a ]' -e 'def t (b : bool) : bool ≔ let not : bool → bool ≔ [ true. ↦ false. | false. ↦ true. ] in let y : bool ≔ not b in ((x p ↦ true.) : (x : bool) → J bool (not x) y → bool) b ?'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ axiom u assumed
  
   ￫ info[I0000]
   ￮ constant J defined
  
   ￫ info[I0000]
   ￮ constant t defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     b : bool
     not ≔ _let.F4.0.not : bool → bool
     y ≔ not b : bool
     ----------------------------------------------------------------------
     J bool (not b) (not b)
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

This also works for a modal let-bound variable used with a key.

  $ narya -v -spatial letcase.ny -e 'def J (A : Type) (a : A) : A → Type ≔ data [ rfl. : J A a a ]' -e 'def t (b : bool) : bool ≔ let not :♭| bool → bool ≔ [ true. ↦ false. | false. ↦ true. ] in ((p ↦ true.) : J bool (not b) b → bool) ?'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ axiom u assumed
  
   ￫ info[I0000]
   ￮ constant J defined
  
   ￫ info[I0000]
   ￮ constant t defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     b : bool
     not ≔ _let.F4.0.not :♭| bool → bool
     ----------------------------------------------------------------------
     J bool (not b) b
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]
