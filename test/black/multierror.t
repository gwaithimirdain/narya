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

A later field whose type only trivially depends on a failed one can still be checked, since its type doesn't actually use the failed field.

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
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/partialmatch5.ny
   10 |   let s : P (g false. true.) ≔ (p : P false.) in
      ^ term synthesized type
          P true.
        but is being checked against type
          P false.
        unequal constructors:
          true
        does not equal
          false
  
  [1]

An ascription in checking position that is a valid type, but disagrees with the checking type, is reported once.  The term is then checked against the ascription, since that's what the user said its type should be.  If that succeeds, there is nothing more to report.

  $ cat >ascmismatch.ny <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > axiom P : Bool → Type
  > axiom p : P true.
  > axiom q : P false.
  > def prod (X Y : Type) : Type ≔ sig ( fst : X, snd : Y )
  > EOF

  $ narya ascmismatch.ny -e 'def t1 : P false. ≔ (p : P true.)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t1 : P false. ≔ (p : P true.)
     ^ term synthesized type
         P true.
       but is being checked against type
         P false.
       unequal constructors:
         true
       does not equal
         false
  
  [1]

  $ narya ascmismatch.ny -e 'def t2 : Bool ≔ ((x ↦ x) : Bool → Bool)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t2 : Bool ≔ ((x ↦ x) : Bool → Bool)
     ^ term synthesized type
         Bool → Bool
       but is being checked against type
         Bool
       unequal head terms:
         Bool → Bool
       does not equal
         Bool
  
  [1]

If the term also fails to check against the ascription, but does check against the checking type, we report both errors, and checking continues with the well-typed term.

  $ narya ascmismatch.ny -e 'def t3 : prod (P false.) Bool ≔ ((q : P true.), Type)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t3 : prod (P false.) Bool ≔ ((q : P true.), Type)
     ^ term synthesized type
         P true.
       but is being checked against type
         P false.
       unequal constructors:
         true
       does not equal
         false
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t3 : prod (P false.) Bool ≔ ((q : P true.), Type)
     ^ term synthesized type
         P false.
       but is being checked against type
         P true.
       unequal constructors:
         false
       does not equal
         true
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t3 : prod (P false.) Bool ≔ ((q : P true.), Type)
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
  [1]

If it fails against both, the errors relative to the ascription are reported.

  $ narya ascmismatch.ny -e 'def t4 : Bool ≔ ((x ↦ x) : Bool → P true.)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t4 : Bool ≔ ((x ↦ x) : Bool → P true.)
     ^ term synthesized type
         Bool → P true.
       but is being checked against type
         Bool
       unequal head terms:
         Bool → P true.
       does not equal
         Bool
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t4 : Bool ≔ ((x ↦ x) : Bool → P true.)
     ^ term synthesized type
         Bool
       but is being checked against type
         P true.
       unequal head constants:
         Bool
       does not equal
         P
  
  [1]

If the ascribed type itself has an error, the term is checked against the checking type instead, so that its errors are also reported.  This applies even when the error in the ascription is inside a part, like a record field, that accumulates its errors.

  $ narya ascmismatch.ny -e 'def t5 : Bool ≔ (Type : sig (x : Bool, y : true.))'
   ￫ error[E1000]
   ￭ command-line exec string
   1 | def t5 : Bool ≔ (Type : sig (x : Bool, y : true.))
     ^ non-datatype Type has no constructor named true
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t5 : Bool ≔ (Type : sig (x : Bool, y : true.))
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
  [1]

But if the ascribed type fails only because it depends on something that already failed, the term is not checked against the checking type, since what's wrong is that earlier failure.

  $ narya ascmismatch.ny -e 'def t6 : Bool ≔ let f : Bool → Type ≔ x ↦ match x [ true. ↦ Bool | false. ↦ true. ] in (Type : f false.)'
   ￫ error[E1000]
   ￭ command-line exec string
   1 | def t6 : Bool ≔ let f : Bool → Type ≔ x ↦ match x [ true. ↦ Bool | false. ↦ true. ] in (Type : f false.)
     ^ non-datatype Type has no constructor named true
  
  [1]

A failed empty pattern-matching lambda in one branch of a match doesn't prevent other branches from being checked.

  $ narya -e 'def Bool : Type ≔ data [ true. | false. ]' -e 'def f (b : Bool) : Bool → Bool ≔ match b [ true. ↦ [ ] | false. ↦ x ↦ Type ]'
   ￫ error[E1300]
   ￭ command-line exec string
   1 | def f (b : Bool) : Bool → Bool ≔ match b [ true. ↦ [ ] | false. ↦ x ↦ Type ]
     ^ missing match clause for constructor true
  
   ￫ error[E1300]
   ￭ command-line exec string
   1 | def f (b : Bool) : Bool → Bool ≔ match b [ true. ↦ [ ] | false. ↦ x ↦ Type ]
     ^ missing match clause for constructor false
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f (b : Bool) : Bool → Bool ≔ match b [ true. ↦ [ ] | false. ↦ x ↦ Type ]
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
  [1]

Mismatches in cube abstraction symbols are just syntax restrictions, so checking goes on normally after reporting them.

  $ narya -e "axiom A:Type" -e "def sum (X Y:Type) : Type ≔ data [ left. (_:X) | right. (_:Y) ]" -e "def foo (u:sum A A) : Type ≔ match u [ left. _ ⤇ A | right. _ ⤇ A ]"
   ￫ error[E0508]
   ￭ command-line exec string
   1 | def foo (u:sum A A) : Type ≔ match u [ left. _ ⤇ A | right. _ ⤇ A ]
     ^ cube abstraction not allowed for zero-dimensional match
  
   ￫ error[E0508]
   ￭ command-line exec string
   1 | def foo (u:sum A A) : Type ≔ match u [ left. _ ⤇ A | right. _ ⤇ A ]
     ^ cube abstraction not allowed for zero-dimensional match
  
  [1]

  $ narya -e "axiom A:Type" -e "def prod (X Y : Type) : Type ≔ sig (fst:X,snd:Y)" -e "def f : prod (A→A) (A→A) ≔ (x ⤇ x, x ⤇ x)"
   ￫ error[E0508]
   ￭ command-line exec string
   1 | def f : prod (A→A) (A→A) ≔ (x ⤇ x, x ⤇ x)
     ^ cube abstraction not allowed for zero-dimensional function
  
   ￫ error[E0508]
   ￭ command-line exec string
   1 | def f : prod (A→A) (A→A) ≔ (x ⤇ x, x ⤇ x)
     ^ cube abstraction not allowed for zero-dimensional function
  
  [1]

Such an error doesn't cause the part of the term containing it to fail, so later parts that depend on it can still be checked.

  $ narya ascmismatch.ny -e 'def r1 : sig (b : Bool → Bool, c : P (b true.)) ≔ (x ⤇ x, q)'
   ￫ error[E0508]
   ￭ command-line exec string
   1 | def r1 : sig (b : Bool → Bool, c : P (b true.)) ≔ (x ⤇ x, q)
     ^ cube abstraction not allowed for zero-dimensional function
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def r1 : sig (b : Bool → Bool, c : P (b true.)) ≔ (x ⤇ x, q)
     ^ term synthesized type
         P false.
       but is being checked against type
         P true.
       unequal constructors:
         false
       does not equal
         true
  
  [1]

The same holds for a wrong ascription on a term that checks against the outer type.

  $ narya ascmismatch.ny -e 'def r2 : sig (b : Bool, c : P b) ≔ ((true. : P true.), q)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def r2 : sig (b : Bool, c : P b) ≔ ((true. : P true.), q)
     ^ term synthesized type
         P true.
       but is being checked against type
         Bool
       unequal head constants:
         P
       does not equal
         Bool
  
   ￫ error[E1000]
   ￭ command-line exec string
   1 | def r2 : sig (b : Bool, c : P b) ≔ ((true. : P true.), q)
     ^ non-datatype P true. has no constructor named true
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def r2 : sig (b : Bool, c : P b) ≔ ((true. : P true.), q)
     ^ term synthesized type
         P false.
       but is being checked against type
         P true.
       unequal constructors:
         false
       does not equal
         true
  
  [1]

However, a speculative check fails if it reports any error at all.  Thus, a calc step is checked in reverse if its proof has any error when checked forwards, and if it also has an error when checked in reverse, the errors from checking it forwards are reported.

  $ cat >calcrev.ny <<EOF
  > axiom A : Type
  > axiom x : A
  > axiom y : A
  > axiom p : Id A y x
  > def yx : Id A x y ≔ calc
  >   x
  >   = y
  >       by ((u ⤇ p) : A → Id A y x) x ∎
  > EOF

  $ narya calcrev.ny
   ￫ error[E0508]
   ￭ $TESTCASE_ROOT/calcrev.ny
   8 |       by ((u ⤇ p) : A → Id A y x) x ∎
     ^ cube abstraction not allowed for zero-dimensional function
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/calcrev.ny
   8 |       by ((u ⤇ p) : A → Id A y x) x ∎
     ^ term synthesized type
         Id A y x
       but is being checked against type
         Id A x y
       unequal head constants:
         y
       does not equal
         x
  
  [1]

An echo isn't displayed, and neither a definition nor its holes are reported, if there are any errors, even ones that didn't make any part of the term fail.

  $ narya ascmismatch.ny -e 'echo ((x ⤇ x) : Bool → Bool)'
   ￫ error[E0508]
   ￭ command-line exec string
   1 | echo ((x ⤇ x) : Bool → Bool)
     ^ cube abstraction not allowed for zero-dimensional function
  
  [1]

  $ narya -v ascmismatch.ny -e 'def h : prod (Bool → Bool) Bool ≔ (x ⤇ x, ?)'
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0001]
   ￮ axiom P assumed
  
   ￫ info[I0001]
   ￮ axiom p assumed
  
   ￫ info[I0001]
   ￮ axiom q assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0508]
   ￭ command-line exec string
   1 | def h : prod (Bool → Bool) Bool ≔ (x ⤇ x, ?)
     ^ cube abstraction not allowed for zero-dimensional function
  
  [1]

Diagnostics emitted during a speculative check that is discarded are not displayed.  Here the term is checked against both its ascription and the outer type, but the hint about the match is only displayed once.

  $ cat >emit.ny <<EOF
  > def Bool : Type ≔ data [ true. | false. ]
  > def M (X : Type) : Type ≔ data [ c. (_ : Bool) ]
  > axiom A : Type
  > axiom B : Type
  > EOF

  $ narya -v emit.ny -e 'def t (b : Bool) : M A ≔ (c. (match b [ true. ↦ false. | false. ↦ true. ]) : M B)'
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant M defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (b : Bool) : M A ≔ (c. (match b [ true. ↦ false. | false. ↦ true. ]) : M B)
     ^ term synthesized type
         M B
       but is being checked against type
         M A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ hint[H0403]
   ￭ command-line exec string
   1 | def t (b : Bool) : M A ≔ (c. (match b [ true. ↦ false. | false. ↦ true. ]) : M B)
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
  [1]

A component of a datatype, codatatype, record type, tuple, or comatch that fails to typecheck is recorded as failed, so that the rest of the term can still be checked and used.  Only things that use the failed component fail, and they fail silently.

  $ cat >failed.ny <<EOF
  > axiom A : Type
  > axiom a : A
  > def Bool : Type ≔ data [ true. | false. ]
  > def P : Bool → Type ≔ [ true. ↦ A | false. ↦ Bool ]
  > EOF

A failed constructor of a datatype makes the corresponding branches of matches fail, but not the other branches.

  $ narya failed.ny -e 'def D : Type ≔ data [ bad. (_ : a) | ok. ] and f (x : D) : Bool ≔ match x [ bad. _ ↦ true. | ok. ↦ a ]'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def D : Type ≔ data [ bad. (_ : a) | ok. ] and f (x : D) : Bool ≔ match x [ bad. _ ↦ true. | ok. ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def D : Type ≔ data [ bad. (_ : a) | ok. ] and f (x : D) : Bool ≔ match x [ bad. _ ↦ true. | ok. ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         Bool
       unequal head constants:
         A
       does not equal
         Bool
  
  [1]

Similarly, a match on that datatype can omit the failed constructor, and using the failed constructor fails silently.

  $ narya failed.ny -e 'def D : Type ≔ data [ bad. (_ : a) | ok. ] and f (x : D) : Bool ≔ match x [ ok. ↦ true. ] and g : D ≔ bad. a and h : D ≔ ok. a'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def D : Type ≔ data [ bad. (_ : a) | ok. ] and f (x : D) : Bool ≔ match x [ ok. ↦ true. ] and g : D ≔ bad. a and h : D ≔ ok. a
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E1001]
   ￭ command-line exec string
   1 | def D : Type ≔ data [ bad. (_ : a) | ok. ] and f (x : D) : Bool ≔ match x [ ok. ↦ true. ] and g : D ≔ bad. a and h : D ≔ ok. a
     ^ too many arguments to constructor ok (1 extra)
  
  [1]

A duplicate constructor is reported, but the first one can still be used.

  $ narya failed.ny -e 'def D : Type ≔ data [ c. | c. (_ : a) ] and f : D ≔ c.'
   ￫ error[E1503]
   ￭ command-line exec string
   1 | def D : Type ≔ data [ c. | c. (_ : a) ] and f : D ≔ c.
     ^ duplicate constructor in datatype: c
  
  [1]

A failed field of a record type or codatatype fails only the projections of that field.

  $ narya failed.ny -e 'def R : Type ≔ sig (x : a, y : Bool, z : Bool) and f : R ≔ (Type, true., a) and g (s : R) : A ≔ s .z'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def R : Type ≔ sig (x : a, y : Bool, z : Bool) and f : R ≔ (Type, true., a) and g (s : R) : A ≔ s .z
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def R : Type ≔ sig (x : a, y : Bool, z : Bool) and f : R ≔ (Type, true., a) and g (s : R) : A ≔ s .z
     ^ term synthesized type
         A
       but is being checked against type
         Bool
       unequal head constants:
         A
       does not equal
         Bool
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def R : Type ≔ sig (x : a, y : Bool, z : Bool) and f : R ≔ (Type, true., a) and g (s : R) : A ≔ s .z
     ^ term synthesized type
         Bool
       but is being checked against type
         A
       unequal head constants:
         Bool
       does not equal
         A
  
  [1]

  $ narya failed.ny -e 'def S : Type ≔ codata [ s .x : a | s .y : Bool ] and f (s : S) : A ≔ s .y'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def S : Type ≔ codata [ s .x : a | s .y : Bool ] and f (s : S) : A ≔ s .y
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def S : Type ≔ codata [ s .x : a | s .y : Bool ] and f (s : S) : A ≔ s .y
     ^ term synthesized type
         Bool
       but is being checked against type
         A
       unequal head constants:
         Bool
       does not equal
         A
  
  [1]

A failed field of a tuple fails only the things that need its value.  Here the second field is used, so its error is found.

  $ narya failed.ny -e 'def f : A ≔ let s : sig (x : Bool, y : Bool) ≔ (a, true.) in (true. : P (s .y))'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : A ≔ let s : sig (x : Bool, y : Bool) ≔ (a, true.) in (true. : P (s .y))
     ^ term synthesized type
         A
       but is being checked against type
         Bool
       unequal head constants:
         A
       does not equal
         Bool
  
   ￫ error[E1000]
   ￭ command-line exec string
   1 | def f : A ≔ let s : sig (x : Bool, y : Bool) ≔ (a, true.) in (true. : P (s .y))
     ^ non-datatype A has no constructor named true
  
  [1]

But here the value of the first field is needed, so the second error fails silently.

  $ narya failed.ny -e 'def f : A ≔ let s : sig (x : Bool, y : Bool) ≔ (a, true.) in (true. : P (s .x))'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : A ≔ let s : sig (x : Bool, y : Bool) ≔ (a, true.) in (true. : P (s .x))
     ^ term synthesized type
         A
       but is being checked against type
         Bool
       unequal head constants:
         A
       does not equal
         Bool
  
  [1]

A missing field is treated like a failed one.

  $ narya failed.ny -e 'def f : sig (x : Bool, y : Bool) ≔ (y ≔ a)'
   ￫ error[E0902]
   ￭ command-line exec string
   1 | def f : sig (x : Bool, y : Bool) ≔ (y ≔ a)
     ^ record field 'x' missing in tuple
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : sig (x : Bool, y : Bool) ≔ (y ≔ a)
     ^ term synthesized type
         A
       but is being checked against type
         Bool
       unequal head constants:
         A
       does not equal
         Bool
  
  [1]

A failed method of a comatch doesn't prevent the other methods from being checked, even corecursively.

  $ narya failed.ny -e 'def S : Type ≔ codata [ s .head : Bool | s .tail : S ] and f : S ≔ [ .head ↦ a | .tail ↦ g ] and g : S ≔ [ .head ↦ true. | .tail ↦ a ]'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def S : Type ≔ codata [ s .head : Bool | s .tail : S ] and f : S ≔ [ .head ↦ a | .tail ↦ g ] and g : S ≔ [ .head ↦ true. | .tail ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         Bool
       unequal head constants:
         A
       does not equal
         Bool
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def S : Type ≔ codata [ s .head : Bool | s .tail : S ] and f : S ≔ [ .head ↦ a | .tail ↦ g ] and g : S ≔ [ .head ↦ true. | .tail ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         S
       unequal head constants:
         A
       does not equal
         S
  
  [1]

A failed modal field keeps its modality, so projecting it with the right locking modality fails silently, while projecting it with the wrong one is still an error.

  $ narya -spatial -e "axiom A : Type" -e "axiom a : A" -e "def C : Type ≔ codata [ (x :♭| _) .fld : a | x .g : A ] and f (c :♭| C) : A ≔ (c :♭| _) .fld"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def C : Type ≔ codata [ (x :♭| _) .fld : a | x .g : A ] and f (c :♭| C) : A ≔ (c :♭| _) .fld
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
  [1]

  $ narya -spatial -e "axiom A : Type" -e "axiom a : A" -e "def C : Type ≔ codata [ (x :♭| _) .fld : a | x .g : A ] and f (c :♭| C) : A ≔ (c :♯| _) .fld"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def C : Type ≔ codata [ (x :♭| _) .fld : a | x .g : A ] and f (c :♭| C) : A ≔ (c :♯| _) .fld
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E1712]
   ￭ command-line exec string
   1 | def C : Type ≔ codata [ (x :♭| _) .fld : a | x .g : A ] and f (c :♭| C) : A ≔ (c :♯| _) .fld
     ^ field fld is modal with left adjoint ♭, but was projected with locking modality ♯
  
  [1]

A failing definition in a mutual block doesn't prevent the later ones from being checked.  If its term fails, the later ones can still use its type, but anything that needs its value fails silently.

  $ narya failed.ny -e 'def f : A ≔ true. and g : A ≔ f and h : A ≔ Type'
   ￫ error[E1000]
   ￭ command-line exec string
   1 | def f : A ≔ true. and g : A ≔ f and h : A ≔ Type
     ^ non-datatype A has no constructor named true
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : A ≔ true. and g : A ≔ f and h : A ≔ Type
     ^ term synthesized type
         Type
       but is being checked against type
         A
       unequal head terms:
         Type
       does not equal
         A
  
  [1]

  $ narya failed.ny -e 'def f : Bool ≔ Type and g : P f ≔ a and h : A ≔ Type'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : Bool ≔ Type and g : P f ≔ a and h : A ≔ Type
     ^ term synthesized type
         Type
       but is being checked against type
         Bool
       unequal head terms:
         Type
       does not equal
         Bool
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : Bool ≔ Type and g : P f ≔ a and h : A ≔ Type
     ^ term synthesized type
         Type
       but is being checked against type
         A
       unequal head terms:
         Type
       does not equal
         A
  
  [1]

If its type fails, then anything that uses it fails silently.

  $ narya failed.ny -e 'def f : a ≔ a and g : f ≔ a and h : A ≔ Type'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : a ≔ a and g : f ≔ a and h : A ≔ Type
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : a ≔ a and g : f ≔ a and h : A ≔ Type
     ^ term synthesized type
         Type
       but is being checked against type
         A
       unequal head terms:
         Type
       does not equal
         A
  
  [1]

The same goes for a synthesizing definition.

  $ narya failed.ny -e 'def f ≔ (a : Bool) and h : A ≔ Type'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f ≔ (a : Bool) and h : A ≔ Type
     ^ term synthesized type
         A
       but is being checked against type
         Bool
       unequal head constants:
         A
       does not equal
         Bool
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f ≔ (a : Bool) and h : A ≔ Type
     ^ term synthesized type
         Type
       but is being checked against type
         A
       unequal head terms:
         Type
       does not equal
         A
  
  [1]

When checking a file, a failing command doesn't prevent later commands from being checked.  As in a mutual block, if a definition fails, later commands can still use its type, but anything that needs its value fails silently; and if the type of a definition or axiom fails, anything that uses it fails silently.

  $ cat >cmds.ny <<EOF
  > axiom A : Type
  > axiom a : A
  > def Bool : Type ≔ data [ true. | false. ]
  > def f : A ≔ true.
  > def g : A ≔ f
  > echo f
  > axiom b : a
  > def h : b ≔ a
  > def k : A ≔ Type
  > EOF

  $ narya -v cmds.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ error[E1000]
   ￭ $TESTCASE_ROOT/cmds.ny
   4 | def f : A ≔ true.
     ^ non-datatype A has no constructor named true
  
   ￫ info[I0000]
   ￮ constant g defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/cmds.ny
   7 | axiom b : a
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/cmds.ny
   9 | def k : A ≔ Type
     ^ term synthesized type
         Type
       but is being checked against type
         A
       unequal head terms:
         Type
       does not equal
         A
  
  [1]

A failed argument of a function or constructor doesn't prevent the other arguments from being checked, as long as their types don't depend on it.  The output type of the application can also be used if it doesn't depend on the failed argument.

  $ cat >args.ny <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom C : Type
  > axiom a : A
  > axiom c : C
  > def List (X : Type) : Type ≔ data [ nil. | cons. (x : X) (xs : List X) ]
  > EOF

  $ narya args.ny -e 'axiom f : A → C → A' -e 'def t : C ≔ f c a'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : C ≔ f c a
     ^ term synthesized type
         C
       but is being checked against type
         A
       unequal head constants:
         C
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : C ≔ f c a
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : C ≔ f c a
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
  [1]

Here the type of the second argument depends on the first, so its error fails silently.

  $ narya args.ny -e 'axiom f : (x : A) → B x → C' -e 'def t : C ≔ f c a'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : C ≔ f c a
     ^ term synthesized type
         C
       but is being checked against type
         A
       unequal head constants:
         C
       does not equal
         A
  
  [1]

Here the second argument can be checked, but the output type depends on the first, so checking it against the expected type fails silently.

  $ narya args.ny -e 'axiom f : (x : A) → C → B x' -e 'def t : B a ≔ f c a'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : B a ≔ f c a
     ^ term synthesized type
         C
       but is being checked against type
         A
       unequal head constants:
         C
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : B a ≔ f c a
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
  [1]

The same goes for constructors.

  $ narya args.ny -e 'def t : List A ≔ cons. c (cons. c nil.)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : List A ≔ cons. c (cons. c nil.)
     ^ term synthesized type
         C
       but is being checked against type
         A
       unequal head constants:
         C
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : List A ≔ cons. c (cons. c nil.)
     ^ term synthesized type
         C
       but is being checked against type
         A
       unequal head constants:
         C
       does not equal
         A
  
  [1]

A let-binding whose value or type fails to typecheck binds the variable to an error, so that the parts of the body that use it fail silently, while the others can still be checked.

  $ cat >let.ny <<EOF
  > axiom A : Type
  > axiom B : Type
  > axiom a : A
  > axiom b : B
  > def Bool : Type ≔ data [ true. | false. ]
  > EOF

  $ narya let.ny -e 'def t : A ≔ let x : A ≔ b in (b : A)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let x : A ≔ b in (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let x : A ≔ b in (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
  [1]

  $ narya let.ny -e 'def t : A ≔ let x : b ≔ a in (b : A)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let x : b ≔ a in (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let x : b ≔ a in (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
  [1]

  $ narya let.ny -e 'def t : A ≔ let x : A ≔ b in x'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let x : A ≔ b in x
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
  [1]

This also works across a match in the body, and a let-binding of a case tree.

  $ narya let.ny -e 'def t (u : Bool) : A ≔ let x : A ≔ b in match u [ true. ↦ x | false. ↦ (b : A) ]'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (u : Bool) : A ≔ let x : A ≔ b in match u [ true. ↦ x | false. ↦ (b : A) ]
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (u : Bool) : A ≔ let x : A ≔ b in match u [ true. ↦ x | false. ↦ (b : A) ]
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
  [1]

  $ narya let.ny -e 'def t : Bool → A ≔ let x : A ≔ b in let f : Bool → A ≔ [ true. ↦ x | false. ↦ (b : A) ] in f'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : Bool → A ≔ let x : A ≔ b in let f : Bool → A ≔ [ true. ↦ x | false. ↦ (b : A) ] in f
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : Bool → A ≔ let x : A ≔ b in let f : Bool → A ≔ [ true. ↦ x | false. ↦ (b : A) ] in f
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
  [1]

In a let-rec, a variable whose value fails to typecheck can still be used for its type, by the body and by the other values, but anything that needs its value fails silently.

  $ narya let.ny -e 'def t : A ≔ let rec f : Bool → A ≔ x ↦ (b : A) and g : Bool → A ≔ x ↦ f x in (g true. : B)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let rec f : Bool → A ≔ x ↦ (b : A) and g : Bool → A ≔ x ↦ f x in (g true. : B)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let rec f : Bool → A ≔ x ↦ (b : A) and g : Bool → A ≔ x ↦ f x in (g true. : B)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let rec f : Bool → A ≔ x ↦ (b : A) and g : Bool → A ≔ x ↦ f x in (g true. : B)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]

  $ narya let.ny -e 'def t : A ≔ let rec f : A ≔ (b : A) and g : Id A f a ≔ refl a in (b : A)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let rec f : A ≔ (b : A) and g : Id A f a ≔ refl a in (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let rec f : A ≔ (b : A) and g : Id A f a ≔ refl a in (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
  [1]

A variable whose type fails to typecheck is an error, so its value isn't checked, and the later types, values, and parts of the body that use it fail silently, while the others can still be checked.

  $ narya let.ny -e 'axiom h : A → A → A' -e 'def t : A ≔ let rec x : b ≔ a and y : x ≔ a and z : A ≔ (b : A) in h x (b : A)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let rec x : b ≔ a and y : x ≔ a and z : A ≔ (b : A) in h x (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let rec x : b ≔ a and y : x ≔ a and z : A ≔ (b : A) in h x (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t : A ≔ let rec x : b ≔ a and y : x ≔ a and z : A ≔ (b : A) in h x (b : A)
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
  [1]

If some parameters of a definition or axiom fail to typecheck, the later parameters and the type are still checked, although those that use the failed parameters fail silently.  The constant is still an error.

  $ narya let.ny -e 'def t (x : b) (y : x) (z : a) : b ≔ a  axiom u (x : b) (z : a) : b  echo t'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (x : b) (y : x) (z : a) : b ≔ a  axiom u (x : b) (z : a) : b  echo t
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (x : b) (y : x) (z : a) : b ≔ a  axiom u (x : b) (z : a) : b  echo t
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (x : b) (y : x) (z : a) : b ≔ a  axiom u (x : b) (z : a) : b  echo t
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (x : b) (y : x) (z : a) : b ≔ a  axiom u (x : b) (z : a) : b  echo t
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (x : b) (y : x) (z : a) : b ≔ a  axiom u (x : b) (z : a) : b  echo t
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def t (x : b) (y : x) (z : a) : b ≔ a  axiom u (x : b) (z : a) : b  echo t
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
  [1]

Similarly, if the domain of a pi-type fails to typecheck, its codomain is still checked, although whatever uses the variable fails silently.  The pi-type itself still fails.

  $ narya let.ny -e 'def f : (x : a) → b ≔ ?  def g : (x : b) → A → x ≔ ?  echo g'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : (x : a) → b ≔ ?  def g : (x : b) → A → x ≔ ?  echo g
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : (x : a) → b ≔ ?  def g : (x : b) → A → x ≔ ?  echo g
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f : (x : a) → b ≔ ?  def g : (x : b) → A → x ≔ ?  echo g
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
  [1]

An unbound identifier is reported when the typechecker reaches it, so that other errors elsewhere in the term are still reported.

  $ narya let.ny -e 'def f (x : Foo) : Bar ≔ x  def g : A ≔ ((y ↦ y) : B → B) zz  echo qq'
   ￫ error[E0300]
   ￭ command-line exec string
   1 | def f (x : Foo) : Bar ≔ x  def g : A ≔ ((y ↦ y) : B → B) zz  echo qq
     ^ unbound variable: Foo
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | def f (x : Foo) : Bar ≔ x  def g : A ≔ ((y ↦ y) : B → B) zz  echo qq
     ^ unbound variable: Bar
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | def f (x : Foo) : Bar ≔ x  def g : A ≔ ((y ↦ y) : B → B) zz  echo qq
     ^ unbound variable: zz
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def f (x : Foo) : Bar ≔ x  def g : A ≔ ((y ↦ y) : B → B) zz  echo qq
     ^ term synthesized type
         B
       but is being checked against type
         A
       unequal head constants:
         B
       does not equal
         A
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | def f (x : Foo) : Bar ≔ x  def g : A ≔ ((y ↦ y) : B → B) zz  echo qq
     ^ unbound variable: qq
  
  [1]
