A let-only binds some variables whose values are defined in the ambient context, but they are the *only* variables in the context of their types and the body.

  $ cat >letonly.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
  > def Vec (A : Type) : ℕ → Type ≔ data [ nil. : Vec A zero. | cons. (n : ℕ) (_ : A) (_ : Vec A n) : Vec A (suc. n) ]
  > def f (n : ℕ) : ℕ ≔ let only m : ℕ ≔ n in (suc. m : ℕ)
  > def g (A : Type) (a : A) : Vec A 1 ≔ let only B : Type ≔ A and b : B ≔ a in (cons. 0 b nil. : Vec B 1)
  > def h (A : Type) (a : A) ≔ let only B : Type ≔ A and b : B ≔ a in b
  > def pred (n : ℕ) : ℕ ≔ let only m : ℕ ≔ n in (match m [ zero. ↦ zero. | suc. k ↦ k ] : ℕ)
  > def two : ℕ ≔ let only m : ℕ ≔ (match (3 : ℕ) [ zero. ↦ zero. | suc. k ↦ k ]) in m
  > EOF

  $ narya -v letonly.ny -e 'echo f 2' -e 'echo g ℕ 0' -e 'synth h' -e 'echo pred 3' -e 'echo pred' -e 'echo two'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant Vec defined
  
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant g defined
  
   ￫ info[I0000]
   ￮ constant h defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/letonly.ny
   6 | def pred (n : ℕ) : ℕ ≔ let only m : ℕ ≔ n in (match m [ zero. ↦ zero. | suc. k ↦ k ] : ℕ)
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant pred defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/letonly.ny
   7 | def two : ℕ ≔ let only m : ℕ ≔ (match (3 : ℕ) [ zero. ↦ zero. | suc. k ↦ k ]) in m
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant two defined
  
  3
    : ℕ
  
  cons. 0 0 nil.
    : Vec ℕ 1
  
  h
    : (A : Type) (a : A) → A
  
  2
    : ℕ
  
  pred
    : (n : ℕ) → ℕ
  
  2
    : ℕ
  

The synthesized type of a let-only is that of its body, with the bound terms substituted.  A let-only is displayed as such if it isn't normalized.

  $ narya letonly.ny -e 'synth let only B : Type ≔ ℕ and b : B ≔ 0 in b'
  let only B : Type ≔ ℕ and b : B ≔ 0 in b
    : ℕ
  

The type of the body is retained, so that if the body doesn't synthesize by itself, it is displayed with an ascription and the result re-parses.

  $ narya letonly.ny -e 'synth let only B : Type ≔ ℕ and b : B ≔ 0 in (cons. 0 b nil. : Vec B 1)' -e 'synth let only B : Type ≔ ℕ and b : B ≔ 0 in ((x ↦ x) : B → B) b' -e 'synth let only B : Type ≔ ℕ and b : B ≔ 0 in ((x ↦ x) b : B)'
  let only B : Type ≔ ℕ and b : B ≔ 0 in (cons. 0 b nil. : Vec B 1)
    : Vec ℕ 1
  
  let only B : Type ≔ ℕ and b : B ≔ 0 in ((x ↦ x) b : B)
    : ℕ
  
  let only B : Type ≔ ℕ and b : B ≔ 0 in ((x ↦ x) b : B)
    : ℕ
  

It computes correctly when degenerated.

  $ narya letonly.ny -e 'def k (A : Type) (x : A) : A ≔ let only B : Type ≔ A and b : B ≔ x in b' -e 'echo (A : Type) (a0 a1 : A) (a2 : Id A a0 a1) ↦ refl (k A) a2'
  A a0 a1 a2 ↦ a2
    : (A : Type) (a0 : A) (a1 : A) (a2 : Id A a0 a1) → Id A a0 a1
  

Variables of the ambient context are not in scope in the types or the body, nor are the bound variables in scope in the bound terms.

  $ narya letonly.ny -e 'def h1 (A : Type) (a : A) ≔ let only b : A ≔ a in b'
   ￫ error[E0300]
   ￭ command-line exec string
   1 | def h1 (A : Type) (a : A) ≔ let only b : A ≔ a in b
     ^ unbound variable: A
  
  [1]

  $ narya letonly.ny -e 'def h2 (A : Type) (a : A) ≔ let only B : Type ≔ A and b : B ≔ a in a'
   ￫ error[E0300]
   ￭ command-line exec string
   1 | def h2 (A : Type) (a : A) ≔ let only B : Type ≔ A and b : B ≔ a in a
     ^ unbound variable: a
  
  [1]

  $ narya letonly.ny -e 'def h3 (A : Type) (a : A) ≔ let only B : Type ≔ A and b : B ≔ a and c : B ≔ b in c'
   ￫ error[E0300]
   ￭ command-line exec string
   1 | def h3 (A : Type) (a : A) ≔ let only B : Type ≔ A and b : B ≔ a and c : B ≔ b in c
     ^ unbound variable: b
  
  [1]

The bound terms are checked at the types with the previous bound terms substituted.

  $ narya letonly.ny -e 'def h4 (A : Type) (a : A) : A ≔ let only B : Type ≔ A and b : B ≔ 0 in b'
   ￫ error[E1000]
   ￭ command-line exec string
   1 | def h4 (A : Type) (a : A) : A ≔ let only B : Type ≔ A and b : B ≔ 0 in b
     ^ non-datatype A has no constructor named zero
  
  [1]

The body must synthesize, and its type, with the bound terms substituted, must match the expected one.

  $ narya letonly.ny -e 'def h5 (n : ℕ) : ℕ ≔ let only m : ℕ ≔ n in suc. m'
   ￫ error[E0400]
   ￭ command-line exec string
   1 | def h5 (n : ℕ) : ℕ ≔ let only m : ℕ ≔ n in suc. m
     ^ non-synthesizing term in synthesizing position (body of let-only)
  
  [1]

  $ narya letonly.ny -e 'def h6 (A : Type) (a : A) : ℕ ≔ let only B : Type ≔ A and b : B ≔ a in b'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def h6 (A : Type) (a : A) : ℕ ≔ let only B : Type ≔ A and b : B ≔ a in b
     ^ term synthesized type
         A
       but is being checked against type
         ℕ
       unequal head terms:
         A
       does not equal
         ℕ
  
  [1]

The variables in the body are free, so we can't match on one belonging to a variable type.

  $ narya letonly.ny -e 'def h7 (A : Type) (a : A) : A ≔ let only B : Type ≔ A and b : B ≔ a in (match b [ ] : B)'
   ￫ error[E1200]
   ￭ command-line exec string
   1 | def h7 (A : Type) (a : A) : A ≔ let only B : Type ≔ A and b : B ≔ a in (match b [ ] : B)
     ^ can't match on variable belonging to non-datatype B
  
  [1]

Holes in the types and body see only the bound variables, while holes in the bound terms see the ambient context.

  $ narya -v -e 'def h8 (A : Type) (a : A) : A ≔ let only B : Type ≔ A and b : B ≔ ? in (? : B)'
   ￫ info[I0000]
   ￮ constant h8 defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     A : Type
     a : A
     ----------------------------------------------------------------------
     A
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     B : Type
     b : B
     ----------------------------------------------------------------------
     B
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

Bound variables can be modal.

  $ cat >modal.ny <<EOF
  > def f (A :♭| Type) (x :♭| A) : A ≔ x
  > def g (A :♭| Type) (x :♭| A) : A ≔ let only B :♭| Type ≔ A and y :♭| B ≔ x in f B y
  > def ♭ (A :♭| Type) : Type ≔ data [ ♭. (x :♭| A) ]
  > def h (A :♭| Type) (x :♭| A) : ♭ A ≔ let only B :♭| Type ≔ A and y :♭| B ≔ x in (♭. y : ♭ B)
  > EOF

  $ narya -v -coreflector modal.ny -e 'synth let only B :♭| Type ≔ Type in B'
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant g defined
  
   ￫ info[I0000]
   ￮ constant ♭ defined
  
   ￫ info[I0000]
   ￮ constant h defined
  
  let only B :♭| Type ≔ Type in B
    : Type
  

  $ narya -coreflector modal.ny -e 'def k (A : Type) : Type ≔ let only B :♭| Type ≔ A in B'
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def k (A : Type) : Type ≔ let only B :♭| Type ≔ A in B
     ^ use of id variable behind ♭ lock requires a key
  
  [1]

The word "only" is reserved (it is also used as an import modifier).

  $ narya -e 'def only : Type ≔ Type'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def only : Type ≔ Type
     ^ parse error: invalid syntax
  
  [1]

If the type of a variable synthesizes a higher-dimensional universe, the variable is a cube, and its bound term must synthesize an instantiation of that type, whose boundary supplies the rest of the cube.

  $ cat >higher.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
  > axiom B : Type
  > axiom b0 : B
  > axiom b1 : B
  > axiom b2 : Id B b0 b1
  > axiom b22 : B⁽ᵉᵉ⁾ b2 b2 (refl b0) (refl b1)
  > EOF

  $ narya higher.ny -e 'synth let only x : Id B ≔ b2 in x' -e 'synth let only x : Id B ≔ b2 in x.0' -e 'echo let only x : Id B ≔ b2 in x.1' -e 'synth let only C : Type ≔ B and x : Id C ≔ b2 in x' -e 'synth let only x : B⁽ᵉᵉ⁾ ≔ b22 in x' -e 'synth let only x : B⁽ᵉᵉ⁾ b2 b2 ≔ b22 in x' -e 'synth let only B0 : Type ≔ ℕ and B1 : Type ≔ ℕ and B2 : Id Type B0 B1 ≔ Id ℕ and x : B2 ≔ refl (0 : ℕ) in x'
  let only x : Id B ≔ b2 in x.2
    : Id B b0 b1
  
  let only x : Id B ≔ b2 in x.0
    : B
  
  b1
    : B
  
  let only C : Type ≔ B and x : Id C ≔ b2 in x.2
    : Id B b0 b1
  
  let only x : B⁽ᵉᵉ⁾ ≔ b22 in x.22
    : B⁽ᵉᵉ⁾ b2 b2 (refl b0) (refl b1)
  
  let only x : B⁽ᵉᵉ⁾ b2 b2 ≔ b22 in x.2
    : B⁽ᵉᵉ⁾ b2 b2 (refl b0) (refl b1)
  
  let only B0 : Type ≔ ℕ
  and B1 : Type ≔ ℕ
  and B2 : Type⁽ᵉ⁾ B0 B1 ≔ ℕ⁽ᵉ⁾
  and x : B2 ≔ refl 0 in
  x.2
    : ℕ⁽ᵉ⁾ 0 0
  

  $ narya -v higher.ny -e 'def h : Id B b0 b1 ≔ let only x : Id B ≔ b2 in (? : Id B x.0 x.1)'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b0 assumed
  
   ￫ info[I0001]
   ￮ axiom b1 assumed
  
   ￫ info[I0001]
   ￮ axiom b2 assumed
  
   ￫ info[I0001]
   ￮ axiom b22 assumed
  
   ￫ info[I0000]
   ￮ constant h defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     x.0 : B
     x.1 : B
     x.2 : Id B x.0 x.1
     ----------------------------------------------------------------------
     Id B x.0 x.1
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

  $ narya higher.ny -e 'def k (A : Type) (a0 a1 : A) (a2 : Id A a0 a1) : Id A a0 a1 ≔ let only C : Type ≔ A and x : Id C ≔ a2 in x' -e 'echo k B b0 b1 b2' -e 'echo refl k (Id B) b2 b2 b22'
  b2
    : Id B b0 b1
  
  b22
    : B⁽ᵉᵉ⁾ b2 b2 (refl b0) (refl b1)
  

  $ narya higher.ny -e 'synth let only x : Id B ≔ b0 in x'
   ￫ error[E0709]
   ￭ command-line exec string
   1 | synth let only x : Id B ≔ b0 in x
     ^ invalid higher-dimensional let-only: bound term has a type of dimension 0, which isn't an instantiation of a type of dimension e
  
  [1]

  $ narya higher.ny -e 'synth let only x : Id ℕ ≔ b2 in x'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | synth let only x : Id ℕ ≔ b2 in x
     ^ term synthesized type
         Id B b0 b1
       but is being checked against type
         ℕ⁽ᵉ⁾ b0 b1
       unequal head constants:
         B
       does not equal
         ℕ
  
  [1]

  $ narya higher.ny -e 'synth let only x : Id ℕ ≔ 0 in x'
   ￫ error[E0400]
   ￭ command-line exec string
   1 | synth let only x : Id ℕ ≔ 0 in x
     ^ non-synthesizing term in synthesizing position (bound term of higher-dimensional let-only)
  
  [1]

  $ narya higher.ny -e 'synth let only x : b0 ≔ b0 in x'
   ￫ error[E1500]
   ￭ command-line exec string
   1 | synth let only x : b0 ≔ b0 in x
     ^ synthesizing let-only variable gave non-universe B
  
  [1]

A superscript on the "let" makes the bound terms a higher-dimensional substitution, so that each of them has the dimension of its type plus that of the let-only.  The let-only then has the corresponding dimension too.

  $ narya higher.ny -e 'synth let⁽ᵉ⁾ only C : Type ≔ Id B and c : C ≔ b2 in c' -e 'echo let⁽ᵉ⁾ only C : Type ≔ Id B and c : C ≔ b2 in c' -e 'synth let^^(e) only C : Type ≔ Id B and c : C ≔ b2 in c' -e 'synth let⁽ᵉ⁾ only x : Id B ≔ b22 in x' -e 'echo let⁽ᵉ⁾ only x : Id B ≔ b22 in x'
  let⁽ᵉ⁾ only C : Type ≔ Id B and c : C ≔ b2 in c
    : Id B b0 b1
  
  b2
    : Id B b0 b1
  
  let⁽ᵉ⁾ only C : Type ≔ Id B and c : C ≔ b2 in c
    : Id B b0 b1
  
  let⁽ᵉ⁾ only x : Id B ≔ b22 in x.2
    : B⁽ᵉᵉ⁾ b2 b2 (refl b0) (refl b1)
  
  b22
    : B⁽ᵉᵉ⁾ b2 b2 (refl b0) (refl b1)
  

It agrees with the degeneration of an ordinary let-only.

  $ narya higher.ny -e 'def k (y0 y1 : B) (y2 : Id B y0 y1) : B ≔ let only x : Id B ≔ y2 in x.0' -e 'echo refl k b2 b2 b22' -e 'echo let⁽ᵉ⁾ only x : Id B ≔ b22 in x.0' -e 'echo refl k (refl b0) (refl b1) (sym b22)' -e 'echo let⁽ᵉ⁾ only x : Id B ≔ sym b22 in x.0'
  b2
    : Id B b0 b1
  
  b2
    : Id B b0 b1
  
  refl b0
    : Id B b0 b0
  
  refl b0
    : Id B b0 b0
  

  $ narya higher.ny -e 'synth let⁽ᵉ⁾ only C : Type ≔ B in C'
   ￫ error[E0709]
   ￭ command-line exec string
   1 | synth let⁽ᵉ⁾ only C : Type ≔ B in C
     ^ invalid higher-dimensional let-only: bound term has a type of dimension 0, which isn't an instantiation of a type of dimension e
  
  [1]

  $ narya higher.ny -e 'synth let⁽ᵉᵉ⁾ only c : B ≔ b2 in c'
   ￫ error[E0709]
   ￭ command-line exec string
   1 | synth let⁽ᵉᵉ⁾ only c : B ≔ b2 in c
     ^ invalid higher-dimensional let-only: bound term has a type of dimension e, which isn't an instantiation of a type of dimension ee
  
  [1]

Only a let-only can have a dimension.

  $ narya higher.ny -e 'synth let⁽ᵉ⁾ x ≔ b0 in x'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | synth let⁽ᵉ⁾ x ≔ b0 in x
     ^ parse error: only a let-only can have a dimension
  
  [1]

  $ narya higher.ny -e 'synth let⁽ᵉ⁾ rec x : B ≔ b0 in x'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | synth let⁽ᵉ⁾ rec x : B ≔ b0 in x
     ^ parse error: only a let-only can have a dimension
  
  [1]

Higher variables and substitutions can be modal.

  $ cat >hmodal.ny <<EOF
  > def f1 (A :♭| Type) (a0 a1 :♭| A) (a2 :♭| Id A a0 a1) : Id A a0 a1 ≔ let only B :♭| Type ≔ A and x :♭| Id B ≔ a2 in x
  > def f2 (A :♭| Type) (a0 a1 :♭| A) (a2 :♭| Id A a0 a1) : Id A a0 a1 ≔ let⁽ᵉ⁾ only B :♭| Type ≔ Id A and y :♭| B ≔ a2 in y
  > EOF

  $ narya -v -coreflector hmodal.ny
   ￫ info[I0000]
   ￮ constant f1 defined
  
   ￫ info[I0000]
   ￮ constant f2 defined
  

If the modality is discrete, the bound terms it annotates have the dimension of their type only, and a variable of positive dimension is not allowed.

  $ cat >hdiscrete.ny <<EOF
  > def f3 (A :♭| Type) (a0 :♭| A) (C : Type) (c0 c1 : C) (c2 : Id C c0 c1) : Id C c0 c1 ≔ let⁽ᵉ⁾ only B :♭| Type ≔ A and y :♭| B ≔ a0 and D : Type ≔ Id C and z : D ≔ c2 in z
  > def f4 (A :♭| Type) (a0 :♭| A) (C : Type) (c0 c1 : C) (c2 : Id C c0 c1) : Id A a0 a0 ≔ let⁽ᵉ⁾ only B :♭| Type ≔ A and y :♭| B ≔ a0 and D : Type ≔ Id C and z : D ≔ c2 in y
  > EOF

  $ narya -v -parametric -discrete-coreflector hdiscrete.ny
   ￫ info[I0000]
   ￮ constant f3 defined
  
   ￫ info[I0000]
   ￮ constant f4 defined
  

  $ narya -parametric -discrete-coreflector -e 'def f5 (A :♭| Type) (a0 a1 :♭| A) (a2 :♭| Id A a0 a1) : Id A a0 a1 ≔ let only B :♭| Type ≔ A and x :♭| Id B ≔ a2 in x'
   ￫ error[E0709]
   ￭ command-line exec string
   1 | def f5 (A :♭| Type) (a0 a1 :♭| A) (a2 :♭| Id A a0 a1) : Id A a0 a1 ≔ let only B :♭| Type ≔ A and x :♭| Id B ≔ a2 in x
     ^ invalid higher-dimensional let-only: dimension of variable is not stable under its modality
  
  [1]

In arity zero, a cube variable has no boundary.

  $ cat >arity0.ny <<EOF
  > axiom A : Type
  > axiom a2 : Br A .
  > EOF

  $ narya -v -parametric -arity 0 -direction p,Br arity0.ny -e 'synth let only x : Br A ≔ a2 in x' -e 'synth let⁽ᵖ⁾ only B : Type ≔ Br A and y : B ≔ a2 in y' -e 'def h : Br A . ≔ let only x : Br A ≔ a2 in (? : Br A .)'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
  let only x : Br A ≔ a2 in x.0
    : Br A .
  
  let⁽ᵖ⁾ only B : Type ≔ Br A and y : B ≔ a2 in y
    : Br A .
  
   ￫ info[I0000]
   ￮ constant h defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     x.0 : Br A .
     ----------------------------------------------------------------------
     Br A .
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

A let-only can contain lock and key clauses, separated from the other clauses by "and" like any clause, which make its bound terms a substitution into a context with locks.  The bound terms to the left of a lock are checked in the ambient context with a matching lock (and everything after it) removed.

  $ cat >locks.ny <<EOF
  > def ♭ (A :♭| Type) : Type ≔ data [ ♭. (x :♭| A) ]
  > def h (A :♭| Type) (x :♭| A) : ♭ A ≔ ♭. (let only B :♭| Type ≔ A and lock ♭ and y : B ≔ x in y)
  > def h2 (A :♭| Type) : ♭ (A → A) ≔ ♭. (z ↦ let only B :♭| Type ≔ A and lock ♭ and y : B ≔ z in y)
  > EOF

  $ narya -v -coreflector locks.ny -e 'synth ((A x ↦ ♭. (let only B :♭| Type ≔ A and lock ♭ and y : B ≔ x in y)) : (A :♭| Type) (x :♭| A) → ♭ A)' -e 'synth ((A ↦ ♭. (z ↦ let only B :♭| Type ≔ A and lock ♭ and y : B ≔ z in y)) : (A :♭| Type) → ♭ (A → A))'
   ￫ info[I0000]
   ￮ constant ♭ defined
  
   ￫ info[I0000]
   ￮ constant h defined
  
   ￫ info[I0000]
   ￮ constant h2 defined
  
  A x ↦ ♭. let only B :♭| Type ≔ A and lock ♭ and y : B ≔ x in y
    : (A :♭| Type) (x :♭| A) → ♭ A
  
  A ↦ ♭. (z ↦ let only B :♭| Type ≔ A and lock ♭ and y : B ≔ z in y)
    : (A :♭| Type) → ♭ (A → A)
  

A lock or key clause must be preceded by "and", unless it comes first.

  $ narya -coreflector locks.ny -e 'def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X lock ♭ in A'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X lock ♭ in A
     ^ parse error: invalid syntax
  
  [1]
  $ narya -coreflector locks.ny -e 'def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and lock ♭ key ε in A'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and lock ♭ key ε in A
     ^ parse error: invalid syntax
  
  [1]

Lock and key clauses can also come first, or there can be no ordinary clauses at all.

  $ narya -coreflector locks.ny -e 'synth ((A ↦ ♭. (let only lock ♭ and B :♭| Type ≔ A in B)) : (A :♭| Type) → ♭ Type)' -e 'synth ((A ↦ ♭. (let only lock ♭ in Type)) : (A :♭| Type) → ♭ Type)'
  A ↦ ♭. let only lock ♭ and B :♭| Type ≔ A in B
    : (A :♭| Type) → ♭ Type
  
  A ↦ ♭. let only lock ♭ in Type
    : (A :♭| Type) → ♭ Type
  

The variables in the body context are behind its locks.

  $ narya -v -coreflector locks.ny -e 'def h3 (A :♭| Type) (x :♭| A) : ♭ A ≔ ♭. (let only B :♭| Type ≔ A and lock ♭ and y : B ≔ x in (? : B))'
   ￫ info[I0000]
   ￮ constant ♭ defined
  
   ￫ info[I0000]
   ￮ constant h defined
  
   ￫ info[I0000]
   ￮ constant h2 defined
  
   ￫ info[I0000]
   ￮ constant h3 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     B :♭| Type (locked: ♭)
     y : B
     ----------------------------------------------------------------------
     B
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

  $ narya -coreflector locks.ny -e 'def h4 (A :♭| Type) (x :♭| A) : ♭ Type ≔ ♭. (let only C : Type ≔ A and lock ♭ in C)'
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def h4 (A :♭| Type) (x :♭| A) : ♭ Type ≔ ♭. (let only C : Type ≔ A and lock ♭ in C)
     ^ use of id variable behind ♭ lock requires a key
  
  [1]

In the context of a hole, the variables hidden by a lock (or by a key, including a postfix one) are displayed with a marker, since their names are still in scope.  A constant they shadow is displayed with "_root_".  A hidden variable that is itself shadowed is renamed, and then its new name is not in scope.

  $ cat >hidden.ny <<EOF
  > def ♭ (A :♭| Type) : Type ≔ data [ ♭. (x :♭| A) ]
  > axiom C : Type
  > def k1 (z :♭| Type) : ♭ (Type → Type) ≔ ♭. (z ↦ let only A :♭| Type ≔ ? and lock ♭ in A)
  > def k2 (W :♭| Type) : ♭ (Type → Type) ≔ ♭. (C ↦ (((? : (_root_.C → Type) → Type) #♭) (_ ↦ Type)))
  > def k3 (z′ :♭| Type) : ♭ (Type → Type) ≔ ♭. (z ↦ let only A :♭| Type → Type ≔ (z ↦ (? : Type)) and lock ♭ in Type)
  > EOF

  $ narya -v -coreflector hidden.ny
   ￫ info[I0000]
   ￮ constant ♭ defined
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0000]
   ￮ constant k1 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     z′ :♭| Type (not in scope)
     z : _ (hidden by lock)
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0000]
   ￮ constant k2 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     W :♭| Type (locked: ♭)
     C : _ (hidden by lock)
     ----------------------------------------------------------------------
     (_root_.C → Type) → Type
  
   ￫ info[I0000]
   ￮ constant k3 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?2:
     
     z′ :♭| Type (locked: ♭)
     z″ : _ (hidden by lock, not in scope)
     z : Type
     ----------------------------------------------------------------------
     Type
  
   ￫ error[E3002]
   ￮ file hidden.ny contains open holes
  
  [1]

The ambient context must have a matching lock, and the bound terms to its left can't use the variables after it.

  $ narya -coreflector locks.ny -e 'def k (A : Type) : Type ≔ let only B : Type ≔ A and lock ♭ in B'
   ￫ error[E1716]
   ￭ command-line exec string
   1 | def k (A : Type) : Type ≔ let only B : Type ≔ A and lock ♭ in B
     ^ let-only lock ♭ doesn't match any suffix of context locks id
  
  [1]

  $ narya -coreflector locks.ny -e 'def k : ♭ (Type → Type) ≔ ♭. (z ↦ let only w : Type ≔ z and lock ♭ in w)'
   ￫ error[E0313]
   ￭ command-line exec string
   1 | def k : ♭ (Type → Type) ≔ ♭. (z ↦ let only w : Type ≔ z and lock ♭ in w)
     ^ variable hidden by lock
  
  [1]

  $ narya -coreflector locks.ny -e 'def k : ♭ Type ≔ ♭. (let only w : Type ≔ Type and lock ♮ in w)'
   ￫ error[E1704]
   ￭ command-line exec string
   1 | def k : ♭ Type ≔ ♭. (let only w : Type ≔ Type and lock ♮ in w)
     ^ unknown modality ♮
  
  [1]

A key clause acts on the bound terms to its left, which are checked in the ambient context with locks matching its vertical target replaced by its vertical source.

  $ narya -coreflector locks.ny -e 'def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and lock ♭ and key ε in A' -e 'synth ((X ↦ let only A :♭| Type ≔ X and lock ♭ and key ε in A) : (X :♭| Type) → Type)' -e 'def t2 (X :♭| Type) (Y : Type) (y : Y) : Y ≔ let only A :♭| Type ≔ X and lock ♭ and key ε and C : Type ≔ Y and c : C ≔ y in c' -e 'echo (Y0 Y1 : Type) (Y2 : Id Type Y0 Y1) (y0 : Y0) (y1 : Y1) (y2 : Y2 y0 y1) ↦ refl (t2 Type) Y2 y2'
  X ↦ let only A :♭| Type ≔ X and lock ♭ and key ε in A
    : (X :♭| Type) → Type
  
  Y0 Y1 Y2 y0 y1 y2 ↦ y2
    : (Y0 : Type) (Y1 : Type) (Y2 : Type⁽ᵉ⁾ Y0 Y1) (y0 : Y0) (y1 : Y1)
      (y2 : Y2 y0 y1)
      → Y2 y0 y1
  

  $ narya -coreflector locks.ny -e 'def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and key ♭ in A'
   ￫ error[E1707]
   ￭ command-line exec string
   1 | def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and key ♭ in A
     ^ vertical target ♭ of key ε_1_1 doesn't match any suffix of context locks id
  
  [1]

  $ narya -coreflector locks.ny -e 'def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and lock ♭ and key (ε ε) in A'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and lock ♭ and key (ε ε) in A
     ^ parse error: invalid key
  
  [1]

When ♭ is not idempotent, there are two different keys ♭♭ ⇒ ♭, which give different results.

  $ cat >comonad.ny <<EOF
  > def ♭ (A :♭| Type) : Type ≔ data [ ♭. (_ :♭| A) ]
  > def k1 (A :♭| Type) (x :♭♭| A) : ♭ A ≔ ♭. (let only B :♭♭| Type ≔ A and y :♭♭| B ≔ x and lock ♭ ♭ and key ε.♭ in y)
  > def k2 (A :♭| Type) (x :♭♭| A) : ♭ A ≔ ♭. (let only B :♭♭| Type ≔ A and y :♭♭| B ≔ x and lock ♭ ♭ and key ♭.ε in y)
  > def e1 (A :♭| Type) (x :♭♭| A) : Id (♭ A) (k1 A x) (♭. (x #ε.♭)) ≔ refl (k1 A x)
  > def e2 (A :♭| Type) (x :♭♭| A) : Id (♭ A) (k2 A x) (♭. (x #♭.ε)) ≔ refl (k2 A x)
  > EOF

  $ narya -comonad comonad.ny -e 'echo (A :♭| Type) (x :♭♭| A) ↦ (k1 A x : ♭ A)' -e 'echo (A :♭| Type) (x :♭♭| A) ↦ (k2 A x : ♭ A)' -e 'synth ((A x ↦ ♭. (let only B :♭♭| Type ≔ A and y :♭♭| B ≔ x and lock ♭ ♭ and key ε.♭ in y)) : (A :♭| Type) (x :♭♭| A) → ♭ A)'
  A x ↦ ♭. (x #ε.♭)
    : (A :♭| Type) (x :♭♭| A) → ♭ A
  
  A x ↦ ♭. (x #ε)
    : (A :♭| Type) (x :♭♭| A) → ♭ A
  
  A x ↦
  ♭. let only B :♭♭| Type ≔ A and y :♭♭| B ≔ x and lock ♭♭ and key ε.♭ in y
    : (A :♭| Type) (x :♭♭| A) → ♭ A
  

  $ narya -comonad comonad.ny -e 'def e3 (A :♭| Type) (x :♭♭| A) : Id (♭ A) (k1 A x) (♭. (x #♭.ε)) ≔ refl (k1 A x)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def e3 (A :♭| Type) (x :♭♭| A) : Id (♭ A) (k1 A x) (♭. (x #♭.ε)) ≔ refl (k1 A x)
     ^ term synthesized type
         ♭⁽ᵉ⁾ (Id A) (♭. (x #ε.♭)) (♭. (x #ε.♭))
       but is being checked against type
         ♭⁽ᵉ⁾ (Id A) (♭. (x #ε.♭)) (♭. (x #ε))
       unequal head terms:
         x #ε.♭
       does not equal
         x #ε
  
  [1]

Adjacent locks are displayed as a single lock by their composite modality, but locks separated by other clauses are not.

  $ narya -comonad comonad.ny -e 'synth ((A ↦ ♭. (♭. (let only B :♭♭| Type ≔ A and B2 :♭♭| Type ≔ A and B3 :♭♭| Type ≔ A and lock ♭ and lock ♭ in Type))) : (A :♭♭| Type) → ♭ (♭ Type))' -e 'synth ((A ↦ ♭. (♭. (let only B :♭♭| Type ≔ A and lock ♭ ♭ and key ε.♭ and lock ♭ in Type))) : (A :♭♭| Type) → ♭ (♭ Type))' -e 'synth ((A ↦ ♭. (♭. (let only B :♭♭| Type ≔ A and lock ♭ and C :♭| Type ≔ A and lock ♭ in C))) : (A :♭♭| Type) → ♭ (♭ Type))'
  A ↦
  ♭.
    (♭.
       (let only B :♭♭| Type ≔ A
        and B2 :♭♭| Type ≔ A
        and B3 :♭♭| Type ≔ A
        and lock ♭♭ in
        Type))
    : (A :♭♭| Type) → ♭ (♭ Type)
  
  A ↦
  ♭.
    (♭. (let only B :♭♭| Type ≔ A and lock ♭♭ and key ε.♭ and lock ♭ in Type))
    : (A :♭♭| Type) → ♭ (♭ Type)
  
  A ↦
  ♭.
    (♭.
       (let only B :♭♭| Type ≔ A
        and lock ♭
        and C :♭| Type ≔ A
        and lock ♭ in
        C))
    : (A :♭♭| Type) → ♭ (♭ Type)
  

A composite lock can strip locks with variables between and after them.

  $ narya -v -comonad comonad.ny -e 'def f : (A :♭♭| Type) → ♭ (Type → ♭ (Type → Type)) ≔ A ↦ ♭. (y ↦ ♭. (z ↦ let only B :♭♭| Type ≔ A and lock ♭♭ in B))' -e 'echo (A :♭♭| Type) ↦ (f A : ♭ (Type → ♭ (Type → Type)))' -e 'synth ((A ↦ ♭. (y ↦ ♭. (z ↦ let only B :♭♭| Type ≔ A and lock ♭♭ in B))) : (A :♭♭| Type) → ♭ (Type → ♭ (Type → Type)))' -e 'def g (A :♭♭| Type) : ♭ (Type → ♭ (Type → Type)) ≔ ♭. (y ↦ ♭. (z ↦ let only B :♭♭| Type ≔ (? : Type) and lock ♭♭ in B))'
   ￫ info[I0000]
   ￮ constant ♭ defined
  
   ￫ info[I0000]
   ￮ constant k1 defined
  
   ￫ info[I0000]
   ￮ constant k2 defined
  
   ￫ info[I0000]
   ￮ constant e1 defined
  
   ￫ info[I0000]
   ￮ constant e2 defined
  
   ￫ info[I0000]
   ￮ constant f defined
  
  A ↦ ♭. (y ↦ ♭. (z ↦ A))
    : (A :♭♭| Type) → ♭ (Type → ♭ (Type → Type))
  
  A ↦ ♭. (y ↦ ♭. (z ↦ let only B :♭♭| Type ≔ A and lock ♭♭ in B))
    : (A :♭♭| Type) → ♭ (Type → ♭ (Type → Type))
  
   ￫ info[I0000]
   ￮ constant g defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     A :♭♭| Type (locked: ♭♭)
     y : _ (hidden by lock)
     z : _ (hidden by lock)
     ----------------------------------------------------------------------
     Type
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

Locks can change the mode.

  $ cat >adjunction.ny <<EOF
  > def △ (A :△| Disc) : Type ≔ data [ △. (_ :△| A) ]
  > EOF

  $ narya -adjunction adjunction.ny -e 'synth ((A a ↦ △. (let only B :△| Disc ≔ A and lock △ and y : B ≔ a in y)) : (A :△| Disc) (a :△| A) → △ A)'
  A a ↦ △. let only B :△| Disc ≔ A and lock △ and y : B ≔ a in y
    : (A :△| Disc) (a :△| A) → △ A
  

  $ narya -adjunction adjunction.ny -e 'def k (A :△| Disc) (a :△| A) : △ A ≔ △. (let only B :△| Disc ≔ A and lock □ and y : B ≔ a in y)'
   ￫ error[E1700]
   ￭ command-line exec string
   1 | def k (A :△| Disc) (a :△| A) : △ A ≔ △. (let only B :△| Disc ≔ A and lock □ and y : B ≔ a in y)
     ^ mode mismatch in let-only lock (Type (source of □) ≠ Disc)
  
  [1]

Locks and keys can occur in a higher-dimensional let-only, and a discrete lock filters the dimension of the bound terms to its left.

  $ narya -coreflector locks.ny -e 'synth ((X x0 x1 x2 ↦ let⁽ᵉ⁾ only A :♭| Type ≔ Id X and lock ♭ and key ε and y : A ≔ x2 in y) : (X :♭| Type) (x0 x1 :♭| X) (x2 :♭| Id X x0 x1) → Id X x0 x1)'
  X x0 x1 x2 ↦
  let⁽ᵉ⁾ only A :♭| Type ≔ Id X
  and lock ♭
  and key ε
  and y : A ≔ x2 in
  y
    : (X :♭| Type) (x0 :♭| X) (x1 :♭| X) (x2 :♭| Id X x0 x1) → Id X x0 x1
  

  $ cat >dlocks.ny <<EOF
  > def ♭ (A :♭| Type) : Type ≔ data [ ♭. (x :♭| A) ]
  > def u (A :♭| Type) (a :♭| A) : ♭ (Br A a a) ≔ ♭. (let⁽ᵖ⁾ only B :♭| Type ≔ A and lock ♭ and y : B ≔ rel a in y)
  > EOF

  $ narya -parametric -direction p,rel,Br -discrete-coreflector dlocks.ny -e 'echo (A :♭| Type) (a :♭| A) ↦ (u A a : ♭ (Br A a a))' -e 'synth ((A a ↦ ♭. (let⁽ᵖ⁾ only B :♭| Type ≔ A and lock ♭ and y : B ≔ rel a in y)) : (A :♭| Type) (a :♭| A) → ♭ (Br A a a))'
  A a ↦ ♭. (rel a)
    : (A :♭| Type) (a :♭| A) → ♭ (Br A a a)
  
  A a ↦ ♭. let⁽ᵖ⁾ only B :♭| Type ≔ A and lock ♭ and y : B ≔ rel a in y
    : (A :♭| Type) (a :♭| A) → ♭ (Br A a a)
  

When a let-only is broken across lines, each lock and key clause goes on its own line, like any other clause.

  $ cat >reformat.ny <<EOF
  > def ♭ (A :♭| Type) : Type ≔ data [ ♭. (x :♭| A) ]
  > def h (A :♭| Type) (x :♭| A) : ♭ A ≔ ♭. (let only B :♭| Type ≔ A   and lock   ♭ and y : B ≔ x in y)
  > def h1 (A :♭| Type) (x :♭| A) : ♭ A ≔ ♭. (let only B :♭| Type ≔ A \`comment
  >   and lock {\` c1 \`} ♭ \`comment2
  >   and y : B ≔ x in y)
  > def h2 (A :♭| Type) : ♭ Type ≔ ♭. (let only lock ♭ and B :♭| Type ≔ A in B)
  > def h3 : ♭ Type ≔ ♭. (let only lock ♭ in Type)
  > def t (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and A2 :♭| Type ≔ X and A3 :♭| Type ≔ X and lock ♭ and key ε and A4 : Type ≔ X in A4
  > def t2 (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and lock ♭ and key ε and B :♭| Type ≔ X and lock ♭ and key ε and C : Type ≔ X in C
  > def t3 (X :♭| Type) : Type ≔ let only A :♭| Type ≔ X and A2 :♭| Type ≔ X and A3 :♭| Type ≔ X and lock ♭ and key ε in A3
  > def h5 (A :♭| Type) : ♭ Type ≔ ♭. (let only lock ♭ and key ε and B :♭| Type ≔ A and C :♭| Type ≔ A and D :♭| Type ≔ A in B)
  > EOF

  $ narya -coreflector reformat.ny

  $ cat reformat.ny
  def ♭ (A :♭| Type) : Type ≔ data [ ♭. (x :♭| A) ]
  
  def h (A :♭| Type) (x :♭| A) : ♭ A
    ≔ ♭. (let only B :♭| Type ≔ A and lock ♭ and y : B ≔ x in y)
  
  def h1 (A :♭| Type) (x :♭| A) : ♭ A
    ≔ ♭.
        (let only B :♭| Type ≔ A `comment
         and lock {` c1 `} ♭ `comment2
         and y : B ≔ x in
         y)
  
  def h2 (A :♭| Type) : ♭ Type ≔ ♭. (let only lock ♭ and B :♭| Type ≔ A in B)
  
  def h3 : ♭ Type ≔ ♭. (let only lock ♭ in Type)
  
  def t (X :♭| Type) : Type ≔
    let only A :♭| Type ≔ X
    and A2 :♭| Type ≔ X
    and A3 :♭| Type ≔ X
    and lock ♭
    and key ε
    and A4 : Type ≔ X in
    A4
  
  def t2 (X :♭| Type) : Type ≔
    let only A :♭| Type ≔ X
    and lock ♭
    and key ε
    and B :♭| Type ≔ X
    and lock ♭
    and key ε
    and C : Type ≔ X in
    C
  
  def t3 (X :♭| Type) : Type ≔
    let only A :♭| Type ≔ X
    and A2 :♭| Type ≔ X
    and A3 :♭| Type ≔ X
    and lock ♭
    and key ε in
    A3
  
  def h5 (A :♭| Type) : ♭ Type
    ≔ ♭.
        (let only lock ♭
         and key ε
         and B :♭| Type ≔ A
         and C :♭| Type ≔ A
         and D :♭| Type ≔ A in
         B)

  $ cp reformat.ny reformat2.ny

  $ narya -coreflector reformat2.ny

  $ diff reformat.ny reformat2.ny

The words "lock" and "key" are reserved.

  $ narya -e 'def lock : Type ≔ Type'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def lock : Type ≔ Type
     ^ parse error: invalid syntax
  
  [1]

  $ narya -e 'def key : Type ≔ Type'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def key : Type ≔ Type
     ^ parse error: invalid syntax
  
  [1]
