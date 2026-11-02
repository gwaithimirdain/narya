Placeholders "_" in term positions create unification metavariables.  There is no unification yet, so any command that creates one fails because it is unsolved.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom a : A
  > def x : A ≔ _
  > def f (y : _) : A ≔ a
  > def g (y : A) : A ≔ match y [ _ ↦ _ ]
  > echo (_ : A)
  > def ok : A ≔ a
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
   ￫ info[I0000]
   ￮ constant ok defined
  
  [1]

A unification metavariable is equal only to itself, including in a nontrivial environment, and is displayed by number.

  $ narya -v - <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > def P (Q : Type → Type) (q : Q _) : Q A ≔ q
  > def F (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
  > display let ≔ environments
  > def F' (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
  > def H (a : A) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a → G a ≔ y ↦ y in A
  > EOF
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ error[E0401]
   ￭ stdin
   3 | def P (Q : Type → Type) (q : Q _) : Q A ≔ q
     ^ term synthesized type
         Q ?u0
       but is being checked against type
         Q A
       unequal head terms:
         ?u0
       does not equal
         A
  
   ￫ error[E0401]
   ￭ stdin
   4 | def F (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ term synthesized type
         B a
       but is being checked against type
         B (let only … in ?u1)
       unequal head terms:
         a
       does not equal
         let only … in ?u1
  
   ￫ info[I0101]
   ￮ display set let to environments
  
   ￫ error[E0401]
   ￭ stdin
   6 | def F' (a : A) (b : B a) : Type ≔ let G : A → Type ≔ x ↦ B _ in let k : G a ≔ b in A
     ^ term synthesized type
         B a
       but is being checked against type
         B (let only a : A ≔ a and b : B a ≔ b and x : A ≔ a in ?u2)
       unequal head terms:
         a
       does not equal
         let only a : A ≔ a and b : B a ≔ b and x : A ≔ a in ?u2
  
   ￫ error[E2004]
   ￮ there is 1 unsolved unification metavariable
  
  [1]
