  $ narya -v matchterm.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant plus defined
  
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant plus_is_1 defined
  
  true.
    : bool
  
  false.
    : bool
  
  true.
    : bool
  
  false.
    : bool
  
  false.
    : bool
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant contra defined
  
   ￫ hint[E1101]
   ￭ $TESTCASE_ROOT/matchterm.ny
   12 | def doublematch (n : ℕ) : bool ≔ match n [ zero. ↦ false. | suc. k ↦ match n [ zero. ↦ true. | suc. _ ↦ false. ]]
      ^ match will not refine the goal or context (discriminee is let-bound): n
  
   ￫ info[I0000]
   ￮ constant doublematch defined
  
   ￫ info[I0000]
   ￮ constant doublematch' defined
  
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ info[I0000]
   ￮ constant zero_or_suc defined
  
   ￫ info[I0000]
   ￮ constant plus_zero_or_suc defined
  
   ￫ info[I0000]
   ￮ constant Vec defined
  
   ￫ info[I0000]
   ￮ constant idvec defined
  
   ￫ info[I0000]
   ￮ constant nil_or_cons defined
  
   ￫ info[I0000]
   ￮ constant idvec_nil_or_cons defined
  

  $ narya -v -parametric multi.ny
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant bool.and defined
  
  true.
    : bool
  
  false.
    : bool
  
   ￫ info[I0000]
   ￮ constant plus defined
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0000]
   ￮ constant fib defined
  
  13
    : ℕ
  
  21
    : ℕ
  
   ￫ info[I0000]
   ￮ constant fib' defined
  
   ￫ info[I0000]
   ￮ constant fib'' defined
  
   ￫ info[I0000]
   ￮ constant even defined
  
   ￫ info[I0000]
   ￮ constant minus2 defined
  
  2
    : ℕ
  
   ￫ info[I0000]
   ￮ constant bothzero defined
  
  false.
    : bool
  
  false.
    : bool
  
  true.
    : bool
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant abort1 defined
  
   ￫ info[I0000]
   ￮ constant abort2 defined
  
   ￫ info[I0000]
   ￮ constant Gel defined
  
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/multi.ny
   75 | def ⊤eq⊥ : Id Type ⊤ ⊥ ≔ Gel ⊤ ⊥ [ ]
      ^ matching lambda encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant ⊤eq⊥ defined
  
   ￫ info[I0000]
   ￮ constant foo defined
  
   ￫ info[I0000]
   ￮ constant one_not_even defined
  
   ￫ info[I0000]
   ￮ constant suc_even_not_even defined
  
   ￫ info[I0000]
   ￮ constant suc_even_not_even' defined
  
   ￫ info[I0000]
   ￮ constant sum defined
  
   ￫ info[I0000]
   ￮ constant sum⊥ defined
  
   ￫ info[I0000]
   ￮ constant sum⊥' defined
  
   ￫ info[I0001]
   ￮ axiom oops assumed
  
  sum⊥' Type (inr. oops)
    : Type
  
   ￫ info[I0000]
   ￮ constant sum⊥'' defined
  
   ￫ info[I0000]
   ￮ constant sum⊥''' defined
  
   ￫ info[I0000]
   ￮ constant is_zero defined
  
   ￫ info[I0000]
   ￮ constant is_zero_eq_zero defined
  
   ￫ info[I0000]
   ￮ constant is_zero_eq_zero' defined
  
   ￫ info[I0000]
   ￮ constant is_zero_eq_zero_rev defined
  
   ￫ info[I0000]
   ￮ constant is_zero_eq_zero_rev' defined
  
   ￫ info[I0000]
   ￮ constant bar defined
  
   ￫ info[I0000]
   ￮ constant bar' defined
  
   ￫ info[I0000]
   ￮ constant bar'' defined
  
   ￫ info[I0000]
   ￮ constant baz defined
  
   ￫ info[I0000]
   ￮ constant bazzz defined
  


  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def bool.and (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true. , false. ↦ false. | _ , false. ↦ false. ]'
   ￫ error[E1307]
   ￭ command-line exec string
   1 | def bool.and (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true. , false. ↦ false. | _ , false. ↦ false. ]
     ^ overlapping patterns in match
  
  [1]

  $ narya -e 'axiom A : Type axiom B : Type def AB : Type ≔ data [ left. (_:A) | right. (_:B) ]' -e 'def foo (x y : AB) : AB ≔ match x,y [ left. a, right. b ↦ left. a | left. a, left. b ↦ left. b | left. a, right. b ↦ left. a | right. b, _ ↦ right. b ]'
   ￫ error[E1302]
   ￭ command-line exec string
   1 | def foo (x y : AB) : AB ≔ match x,y [ left. a, right. b ↦ left. a | left. a, left. b ↦ left. b | left. a, right. b ↦ left. a | right. b, _ ↦ right. b ]
     ^ constructor right appears twice in match
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | false. ↦ false. ]'
   ￫ error[E1305]
   ￭ command-line exec string
   1 | def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | false. ↦ false. ]
     ^ wrong number of patterns for match
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true., false., false. ↦ false. ]'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true., false., false. ↦ false. ]
     ^ parse error: invalid match pattern
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def neg (x : bool) : bool ≔ match x [ true. ↦ false. | false. ↦ . ]'
   ￫ error[E1309]
   ￭ command-line exec string
   1 | def neg (x : bool) : bool ≔ match x [ true. ↦ false. | false. ↦ . ]
     ^ invalid refutation: no discriminee has an empty type
  
  [1]

  $ narya -v -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def ⊥ : Type ≔ data [ ]' -e 'def foo (x : ⊥) (y : bool) : ⊥ ≔ match x, y [ ]' -e 'def foo2 (x : ⊥) (y : bool) : ⊥ ≔ match y, x [ ]' -e 'def unit : Type := data [ star. ]' -e 'def foo3 (x : bool) (y : unit) : ⊥ ≔ match x, y [ ]'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant foo defined
  
   ￫ info[I0000]
   ￮ constant foo2 defined
  
   ￫ info[I0000]
   ￮ constant unit defined
  
   ￫ error[E1300]
   ￭ command-line exec string
   1 | def foo3 (x : bool) (y : unit) : ⊥ ≔ match x, y [ ]
     ^ missing match clause for constructor true
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def foo (x : bool) : bool ≔ match x [ true. ↦ false. | false. y ↦ true. ]'
   ￫ error[E1303]
   ￭ command-line exec string
   1 | def foo (x : bool) : bool ≔ match x [ true. ↦ false. | false. y ↦ true. ]
     ^ too many arguments to constructor false in match pattern (1 extra)
  
  [1]


  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def foo (x : bool) : bool ≔ match x [ true. ↦ false. | true. y ↦ true. ]'
   ￫ error[E1306]
   ￭ command-line exec string
   1 | def foo (x : bool) : bool ≔ match x [ true. ↦ false. | true. y ↦ true. ]
     ^ inconsistent patterns in match
  
  [1]
  $ narya -e 'def prod (A B : Type) : Type ≔ data [ pair. (_:A) (_:B) ]' -e 'def proj1 (A B C : Type) (u : prod (prod A B) C) : C ≔ match u [ pair. (pair. x x) x ↦ x ]'
   ￫ error[E1304]
   ￭ command-line exec string
   1 | def proj1 (A B C : Type) (u : prod (prod A B) C) : C ≔ match u [ pair. (pair. x x) x ↦ x ]
     ^ variable name 'x' used more than once in match patterns
  
  [1]

  $ narya -e 'def prod (A B : Type) : Type ≔ data [ pair. (_:A) (_:B) ]' -e 'def proj1 (A B : Type) (u : prod A B) : A ≔ match u return _ ↦ A [ pair. x x ↦ x ]'
   ￫ error[E1304]
   ￭ command-line exec string
   1 | def proj1 (A B : Type) (u : prod A B) : A ≔ match u return _ ↦ A [ pair. x x ↦ x ]
     ^ variable name 'x' used more than once in match patterns
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def foo : bool → bool → bool ≔ [ ]'
   ￫ error[E1300]
   ￭ command-line exec string
   1 | def foo : bool → bool → bool ≔ [ ]
     ^ missing match clause for constructor true
  
  [1]

  $ narya -e 'def bool : Type ≔ data [ true. | false. ]' -e 'def foo : Type → bool → bool ≔ [ ]'
   ￫ error[E1200]
   ￭ command-line exec string
   1 | def foo : Type → bool → bool ≔ [ ]
     ^ can't match on variable belonging to non-datatype Type
  
  [1]

  $ narya -v -parametric -e 'def bool : Type ≔ data [ true. | false. ] def bool.not (x : bool) : bool ≔ match x [ true. ⤇ false. | false. ⤇ true.]'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ error[E0508]
   ￭ command-line exec string
   1 | def bool : Type ≔ data [ true. | false. ] def bool.not (x : bool) : bool ≔ match x [ true. ⤇ false. | false. ⤇ true.]
     ^ cube abstraction not allowed for zero-dimensional match
  
  [1]

  $ narya -v -parametric -e 'def bool : Type ≔ data [ true. | false. ] def bool.and (x y : bool) : bool ≔ match x, y [ true., true. ⤇ true. | true., false. ⤇ false. | false., true. ⤇ false. | false., false. ⤇ false.]'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ error[E0508]
   ￭ command-line exec string
   1 | def bool : Type ≔ data [ true. | false. ] def bool.and (x y : bool) : bool ≔ match x, y [ true., true. ⤇ true. | true., false. ⤇ false. | false., true. ⤇ false. | false., false. ⤇ false.]
     ^ cube abstraction not allowed for zero-dimensional match
  
  [1]

  $ narya -v -parametric -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bar (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : Type ≔ match y2 [ zero. ↦ ℕ | suc. n ↦ bar n.0 n.1 n.2 ]'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ error[E0510]
   ￭ command-line exec string
   1 | def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bar (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : Type ≔ match y2 [ zero. ↦ ℕ | suc. n ↦ bar n.0 n.1 n.2 ]
     ^ e-dimensional match requires cube abstraction
  
  [1]

  $ narya -v -parametric -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bar (x : ℕ) (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : Type ≔ match x, y2 [ zero., zero. ↦ ℕ | zero., suc. n ↦ bar x n.0 n.1 n.2 | suc. _, zero. ↦ ℕ | suc. _, suc. n ↦ bar x n.0 n.1 n.2 ]'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ error[E0510]
   ￭ command-line exec string
   1 | def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bar (x : ℕ) (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : Type ≔ match x, y2 [ zero., zero. ↦ ℕ | zero., suc. n ↦ bar x n.0 n.1 n.2 | suc. _, zero. ↦ ℕ | suc. _, suc. n ↦ bar x n.0 n.1 n.2 ]
     ^ e-dimensional match requires cube abstraction
  
   ￫ error[E0510]
   ￭ command-line exec string
   1 | def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bar (x : ℕ) (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : Type ≔ match x, y2 [ zero., zero. ↦ ℕ | zero., suc. n ↦ bar x n.0 n.1 n.2 | suc. _, zero. ↦ ℕ | suc. _, suc. n ↦ bar x n.0 n.1 n.2 ]
     ^ e-dimensional match requires cube abstraction
  
  [1]

The pattern variables of a higher-dimensional match can be given explicit boundaries, in braces, like the variables of a non-cube higher-dimensional abstraction.

  $ narya -v -parametric pattern-boundary.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant P defined
  
   ￫ info[I0000]
   ￮ constant bar defined
  
   ￫ info[I0000]
   ￮ constant bar′ defined
  
  bar′
    : (y0 : ℕ) (y1 : ℕ) (y2 : ℕ⁽ᵉ⁾ y0 y1) → ℕ
  
  y0 y1 y2 ↦ match y2 [ suc. {m0} {m1} m2 ↦ m0 | zero. ↦ 0 ]
    : (y0 : ℕ) (y1 : ℕ) (y2 : ℕ⁽ᵉ⁾ y0 y1) → ℕ
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
  match a2 [ suc. n ⤇ n.0 | zero. ⤇ 0 ]
    : ℕ
  
  match a2 [ suc. {m0} {m1} m2 ↦ m0 | zero. ↦ 0 ]
    : ℕ
  
  y0 y1 y2 ⤇ match y2.2 [ suc. m2 ⤇ m2.02 | zero. ⤇ refl 0 ]
    : {y0₀ : ℕ} {y0₁ : ℕ} (y0₂ : ℕ⁽ᵉ⁾ y0₀ y0₁) {y1₀ : ℕ} {y1₁ : ℕ}
      (y1₂ : ℕ⁽ᵉ⁾ y1₀ y1₁) {y2₀ : ℕ⁽ᵉ⁾ y0₀ y1₀} {y2₁ : ℕ⁽ᵉ⁾ y0₁ y1₁}
      (y2₂ : ℕ⁽ᵉᵉ⁾ y0₂ y1₂ y2₀ y2₁)
      →⁽ᵉ⁾ ℕ⁽ᵉ⁾ (bar′ y0₀ y1₀ y2₀) (bar′ y0₁ y1₁ y2₁)
  
   ￫ info[I0000]
   ￮ constant baz defined
  
  y0 y1 y2 ↦
  match y2 [
  | suc. {m0} {𝑥} m2 ↦ match m0 [ suc. k ↦ k | zero. ↦ 1 ]
  | zero. ↦ 0]
    : (y0 : ℕ) (y1 : ℕ) (y2 : ℕ⁽ᵉ⁾ y0 y1) → ℕ
  
   ￫ info[I0000]
   ￮ constant qux defined
  
  y0 y1 y2 ↦ match y2 [ pair. {a0} {a1} a2 b ⤇ b.0 ]
    : (y0 : P) (y1 : P) (y2 : P⁽ᵉ⁾ y0 y1) → ℕ
  
   ￫ info[I0000]
   ￮ constant quux defined
  
  y0 y1 y2 ↦
  match refl y2 [
  | suc. {m00} {m01} {m02} {m10} {m11} {m12} {m20} {m21} m22 ↦ m00
  | zero. ↦ 0]
    : (y0 : ℕ) (y1 : ℕ) (y2 : ℕ⁽ᵉ⁾ y0 y1) → ℕ
  
   ￫ info[I0000]
   ￮ constant deep defined
  
  y0 y1 y2 ↦
  match y2 [
  | suc. {m0} {m1} 𝑥 ↦ match 𝑥 [ suc. {k0} {k1} k2 ↦ k1 | zero. ↦ m0 ]
  | zero. ↦ 0]
    : (y0 : ℕ) (y1 : ℕ) (y2 : ℕ⁽ᵉ⁾ y0 y1) → ℕ
  
   ￫ info[I0000]
   ￮ constant multi defined
  
  x y0 y1 y2 ↦
  match x [
  | suc. 𝑥 ↦ match y2 [ suc. {n0} {n1} n2 ↦ n1 | zero. ↦ 1 ]
  | zero. ↦ match y2 [ suc. {m0} {m1} m2 ↦ m0 | zero. ↦ 0 ]]
    : (x : ℕ) (y0 : ℕ) (y1 : ℕ) (y2 : ℕ⁽ᵉ⁾ y0 y1) → ℕ
  

They must be exactly one for each face of the pattern variable's cube.

  $ narya -parametric -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} m2 ↦ m0 ]'
   ￫ error[E1310]
   ￭ command-line exec string
   1 | def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} m2 ↦ m0 ]
     ^ not enough variables in boundary of higher-dimensional pattern variable (need 1 more)
  
  [1]

  $ narya -parametric -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} {m1} {m2} m3 ↦ m0 ]'
   ￫ error[E1310]
   ￭ command-line exec string
   1 | def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} {m1} {m2} m3 ↦ m0 ]
     ^ too many variables in boundary of higher-dimensional pattern variable (1 extra)
  
  [1]

In particular, a zero-dimensional match has no boundary variables to name.

  $ narya -parametric -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (n : ℕ) : ℕ ≔ match n [ zero. ↦ 0 | suc. {m0} m ↦ m0 ]'
   ￫ error[E1310]
   ￭ command-line exec string
   1 | def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (n : ℕ) : ℕ ≔ match n [ zero. ↦ 0 | suc. {m0} m ↦ m0 ]
     ^ too many variables in boundary of higher-dimensional pattern variable (1 extra)
  
  [1]

Boundary variables must be followed by the pattern variable they belong to.

  $ narya -parametric -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} {m1} ↦ 0 ]'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} {m1} ↦ 0 ]
     ^ parse error: boundary pattern variable must be followed by the pattern variable it belongs to
  
  [1]

A branch that leaves any of its pattern variables as a cube still requires the cube abstraction.

  $ narya -parametric -e 'def P : Type ≔ data [ pair. (x : P) (y : P) ] def bad (y0 y1 : P) (y2 : Id P y0 y1) : P ≔ match y2 [ pair. {a0} {a1} a2 b ↦ a0 ]'
   ￫ error[E0510]
   ￭ command-line exec string
   1 | def P : Type ≔ data [ pair. (x : P) (y : P) ] def bad (y0 y1 : P) (y2 : Id P y0 y1) : P ≔ match y2 [ pair. {a0} {a1} a2 b ↦ a0 ]
     ^ e-dimensional match requires cube abstraction
  
  [1]

And all the branches for a single constructor must name the same number of variables, since they all extend the context in the same way.

  $ narya -parametric -e 'def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} {m1} (zero.) ↦ m0 | suc. n ⤇ n.0 ]'
   ￫ error[E1306]
   ￭ command-line exec string
   1 | def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} {m1} (zero.) ↦ m0 | suc. n ⤇ n.0 ]
     ^ inconsistent patterns in match
  
  [1]
