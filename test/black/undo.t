Undo single command

  $ cat >undo.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > echo a
  > undo 1
  > echo a
  > EOF

  $ narya -v -fake-interact undo.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
  a
    : A
  
   ￫ info[I0006]
   ￮ 1 command undone
  
   ￫ error[E0300]
   ￭ undo.ny
   5 | echo a
     ^ unbound variable: a
  

Undo multiple commands

  $ cat >undo2.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > axiom b:A
  > echo a
  > undo 2
  > echo a
  > EOF

  $ narya -v -fake-interact undo2.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
  a
    : A
  
   ￫ info[I0006]
   ￮ 2 commands undone
  
   ￫ error[E0300]
   ￭ undo2.ny
   6 | echo a
     ^ unbound variable: a
  

Undo nothing

  $ cat >no-undo.ny <<EOF
  > undo 1
  > EOF

  $ narya -v -fake-interact no-undo.ny
   ￫ error[E2500]
   ￮ not enough commands to undo
  

Undo notations

  $ cat >undo-notn.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > axiom f : A -> A -> A
  > notation(1) x "+" y := f x y
  > echo a + a
  > undo 1
  > echo a + a
  > EOF

  $ narya -v -fake-interact undo-notn.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
  a + a
    : A
  
   ￫ info[I0006]
   ￮ 1 command undone
  
  a
    : A
  
   ￫ error[E0200]
   ￭ undo-notn.ny
   7 | echo a + a
     ^ parse error: invalid syntax
  

A command that fails is undone, even if it fails only after recording a partial result, so it doesn't count as a command to undo

  $ cat >undo-fail.ny <<EOF
  > axiom A : Type
  > def f : Type := Type Type
  > def B : Type := sig (x : Type, y : Type Type)
  > undo 1
  > echo A
  > EOF

  $ narya -v -fake-interact undo-fail.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ error[E0505]
   ￭ undo-fail.ny
   2 | def f : Type := Type Type
     ^ can't apply/instantiate a zero-dimensional type Type
  
   ￫ error[E0505]
   ￭ undo-fail.ny
   3 | def B : Type := sig (x : Type, y : Type Type)
     ^ can't apply/instantiate a zero-dimensional type Type
  
   ￫ info[I0006]
   ￮ 1 command undone
  
   ￫ error[E0300]
   ￭ undo-fail.ny
   5 | echo A
     ^ unbound variable: A
  

A hole solution that fails is undone

  $ cat >solve-fail.ny <<EOF
  > def S : Type := sig (x : Type, y : Type)
  > def s : S := ?
  > solve 0 := (x := Type)
  > echo s .x
  > EOF

  $ narya -v -fake-interact solve-fail.ny
   ￫ info[I0000]
   ￮ constant S defined
  
   ￫ info[I0000]
   ￮ constant s defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     S
  
   ￫ error[E0902]
   ￭ solve-fail.ny
   3 | solve 0 := (x := Type)
     ^ record field 'y' missing in tuple
  
  s .x
    : Type
  
