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
  > def ♭ (A :♭| Type) : Type ≔ data [ box. (x :♭| A) ]
  > def h (A :♭| Type) (x :♭| A) : ♭ A ≔ let only B :♭| Type ≔ A and y :♭| B ≔ x in (box. y : ♭ B)
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

