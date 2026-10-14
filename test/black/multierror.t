  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom C:Type
  > axiom a:A
  > def prod (X Y : Type) : Type := sig (fst:X, snd:Y)
  > def foo : prod B C := (a,a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod B C := (a,a)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod B C := (a,a)
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom C:Type
  > axiom a:A
  > axiom c:C
  > def prod (X Y : Type) : Type := sig (fst:X, snd:Y)
  > def foo : prod B C := (a,c)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom c assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   7 | def foo : prod B C := (a,c)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]


  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom C:Type
  > axiom a:A
  > def prod (X Y : Type) : Type := sig (fst:X, snd:Y)
  > def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : prod (prod B C) (prod C B) := ((a,a),(a,a))
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom P:B->Type
  > axiom a:A
  > def Sigma (X : Type) (Y : X -> Type) : Type := sig (fst:X, snd:Y fst)
  > def foo : Sigma B P := (a,a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom P assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   6 | def foo : Sigma B P := (a,a)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def bool : Type := data [ true. | false. ]
  > def P : bool -> Type := [ true. |-> A | false. |-> B ]
  > def Sigma (X : Type) (Y : X -> Type) : Type := sig (fst:X, snd:Y fst)
  > def foo : Sigma bool P := (a, a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant P defined
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   7 | def foo : Sigma bool P := (a, a)
     ^ term synthesized type
         A
       but is being checked against type
         bool
       unequal head constants:
         A
       does not equal
         bool
  
  [1]

Even trivial dependency blocks going on, as long as there is the potential for dependency.  Avoiding this would probably involve more laziness in function arguments.

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def Sigma (X : Type) (Y : X -> Type) : Type := sig (fst:X, snd:Y fst)
  > def foo : Sigma B (_ ↦ B) := (a, a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : Sigma B (_ ↦ B) := (a, a)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]


  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def streamB : Type := codata [ x .head : B | x .tail : streamB ]
  > def foo : streamB := [ .head ↦ a | .tail ↦ a ]
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant streamB defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : streamB := [ .head ↦ a | .tail ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : streamB := [ .head ↦ a | .tail ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         streamB
       unequal head constants:
         A
       does not equal
         streamB
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def streamB : Type := codata [ x .head : B | x .tail : streamB ]
  > def foo : B := let x : streamB := [ .head ↦ a | .tail ↦ a ] in x .head
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant streamB defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : B := let x : streamB := [ .head ↦ a | .tail ↦ a ] in x .head
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo : B := let x : streamB := [ .head ↦ a | .tail ↦ a ] in x .head
     ^ term synthesized type
         A
       but is being checked against type
         streamB
       unequal head constants:
         A
       does not equal
         streamB
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom B:Type
  > axiom a:A
  > def bool : Type := data [ true. | false. ]
  > def foo (x : bool) : B := match x [ true. ↦ a | false. ↦ a ]
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo (x : bool) : B := match x [ true. ↦ a | false. ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   5 | def foo (x : bool) : B := match x [ true. ↦ a | false. ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > def foo : Type := data [ true. (_ : a) | false. (_ : a) ]
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def foo : Type := data [ true. (_ : a) | false. (_ : a) ]
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def foo : Type := data [ true. (_ : a) | false. (_ : a) ]
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > def foo : Type := sig (fst : a, snd : a)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def foo : Type := sig (fst : a, snd : a)
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def foo : Type := sig (fst : a, snd : a)
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > axiom B : A -> Type
  > def foo : Type := sig (fst : a, snd : B fst)
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   4 | def foo : Type := sig (fst : a, snd : B fst)
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > def foo : Type := codata [ x .fst : a | x .snd : a ]
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def foo : Type := codata [ x .fst : a | x .snd : a ]
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def foo : Type := codata [ x .fst : a | x .snd : a ]
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
  [1]

  $ cat >multierr.ny <<EOF
  > def Nat : Type := data [ zero. | suc. (_ : Nat) ]
  > axiom f : Nat -> Nat
  > def pred (x : Nat) : Nat := match x [ zero. |-> Nat | suc. y |-> f (pred y) ]
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0000]
   ￮ constant Nat defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def pred (x : Nat) : Nat := match x [ zero. |-> Nat | suc. y |-> f (pred y) ]
     ^ term synthesized type
         Type
       but is being checked against type
         Nat
       unequal head terms:
         Type
       does not equal
         Nat
  
  [1]

  $ cat >multierr.ny <<EOF
  > def color : Type ≔ data [ red. | green. | blue. ]
  > axiom A:Type
  > axiom a:A
  > def foo (x:color) ≔ match x [ red. ↦ (a,a a) | green. ↦ a | blue. ↦ A ]
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0000]
   ￮ constant color defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ hint[E1101]
   ￭ $TESTCASE_ROOT/multierr.ny
   4 | def foo (x:color) ≔ match x [ red. ↦ (a,a a) | green. ↦ a | blue. ↦ A ]
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   4 | def foo (x:color) ≔ match x [ red. ↦ (a,a a) | green. ↦ a | blue. ↦ A ]
     ^ term synthesized type
         Type
       but is being checked against type
         A
       unequal head terms:
         Type
       does not equal
         A
  
   ￫ error[E0900]
   ￭ $TESTCASE_ROOT/multierr.ny
   4 | def foo (x:color) ≔ match x [ red. ↦ (a,a a) | green. ↦ a | blue. ↦ A ]
     ^ checking tuple against non-record type A
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > echo a a : a
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | echo a a : a
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0701]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | echo a a : a
     ^ attempt to apply/instantiate
         a
       of type
         A
       which is not a function-type or universe
  
  [1]

  $ cat >multierr.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > def foo : A ≔ (a, a) : a
  > EOF

  $ narya -v multierr.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def foo : A ≔ (a, a) : a
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0900]
   ￭ $TESTCASE_ROOT/multierr.ny
   3 | def foo : A ≔ (a, a) : a
     ^ checking tuple against non-record type A
  
  [1]

A match with a failed branch records that branch as failed, and checking continues.  Evaluating the match later in the same definition at that branch fails silently, so only the real error is reported.

  $ cat >partialmatch.ny <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def t : Bool ≔
  >   let g : Bool → Type ≔ x ↦ match x [ true. ↦ true. | false. ↦ Bool ] in
  >   ((true. : g true.) : Bool)
  > EOF

  $ narya partialmatch.ny
   ￫ error[E1000]
   ￭ $TESTCASE_ROOT/partialmatch.ny
   3 |   let g : Bool → Type ≔ x ↦ match x [ true. ↦ true. | false. ↦ Bool ] in
     ^ non-datatype Type has no constructor named true
  
  [1]

  $ cat >partialmatch2.ny <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def t : Bool ≔
  >   let g : Bool → Bool ≔ x ↦ match x [ true. ↦ Bool | false. ↦ true. ] in
  >   ((refl true.) : Id Bool (g true.) true.)
  > EOF

  $ narya partialmatch2.ny
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/partialmatch2.ny
   3 |   let g : Bool → Bool ≔ x ↦ match x [ true. ↦ Bool | false. ↦ true. ] in
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
  [1]

The same holds for conversion checking through a failed branch, and for a failed branch of an inner match in a deep match.  But a later error that doesn't depend on the failed branch is still reported, as is evaluation at a branch that didn't fail.

  $ cat >partialmatch3.ny <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > axiom P : Bool → Type
  > axiom p : P true.
  > def t : Bool ≔
  >   let g : Bool → Bool ≔ x ↦ match x [ true. ↦ Bool | false. ↦ true. ] in
  >   let q : P (g true.) ≔ p in
  >   true.
  > EOF

  $ narya partialmatch3.ny
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/partialmatch3.ny
   5 |   let g : Bool → Bool ≔ x ↦ match x [ true. ↦ Bool | false. ↦ true. ] in
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
  [1]

  $ cat >partialmatch4.ny <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )
  > def t : Σ Bool (_ ↦ Bool) ≔
  >   let g : Bool → Bool ≔ x ↦ match x [ true. ↦ Bool | false. ↦ true. ] in
  >   (g true., Bool)
  > EOF

  $ narya partialmatch4.ny
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/partialmatch4.ny
   4 |   let g : Bool → Bool ≔ x ↦ match x [ true. ↦ Bool | false. ↦ true. ] in
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/partialmatch4.ny
   5 |   (g true., Bool)
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
  [1]

  $ cat >partialmatch5.ny <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > axiom P : Bool → Type
  > axiom p : P true.
  > def t : Bool ≔
  >   let g : Bool → Bool → Bool ≔ x y ↦ match x, y [
  >   | true., true. ↦ Bool
  >   | true., false. ↦ true.
  >   | false., _ ↦ true. ] in
  >   let r : P (g true. false.) ≔ p in
  >   let s : P (g false. true.) ≔ (p : P false.) in
  >   let q : P (g true. true.) ≔ p in
  >   true.
  > EOF

  $ narya partialmatch5.ny
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/partialmatch5.ny
   6 |   | true., true. ↦ Bool
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/partialmatch5.ny
   10 |   let s : P (g false. true.) ≔ (p : P false.) in
      ^ term synthesized type
          P false.
        but is being checked against type
          P true.
        unequal constructors:
          false
        does not equal
          true
  
  [1]
