  $ narya -v stream.ny
   ￫ info[I0000]
   ￮ constant Stream defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom s assumed
  
   ￫ info[I0000]
   ￮ constant s0 defined
  
   ￫ info[I0000]
   ￮ constant s0t defined
  
   ￫ info[I0000]
   ￮ constant s1 defined
  
   ￫ info[I0000]
   ￮ constant s2 defined
  
   ￫ info[I0000]
   ￮ constant s' defined
  
   ￫ info[I0000]
   ￮ constant s_is_s' defined
  
   ￫ info[I0000]
   ￮ constant corec defined
  
   ￫ info[I0000]
   ￮ constant s'' defined
  
   ￫ info[I0000]
   ￮ constant ∞eta defined
  
   ￫ info[I0000]
   ￮ constant ∞eta_bisim defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant nats defined
  
   ￫ info[I0000]
   ￮ constant nats0_eq_0 defined
  
   ￫ info[I0000]
   ￮ constant nats1_eq_1 defined
  
   ￫ info[I0000]
   ￮ constant nats2_eq_2 defined
  
   ￫ info[I0000]
   ￮ constant nats3_eq_3 defined
  
   ￫ info[I0000]
   ￮ constant plus defined
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant fib defined
  
   ￫ info[I0000]
   ￮ constant fib0_eq_1 defined
  
   ￫ info[I0000]
   ￮ constant fib1_eq_1 defined
  
   ￫ info[I0000]
   ￮ constant fib2_eq_2 defined
  
   ￫ info[I0000]
   ￮ constant fib3_eq_3 defined
  
   ￫ info[I0000]
   ￮ constant fib4_eq_5 defined
  
   ￫ info[I0000]
   ￮ constant fib5_eq_8 defined
  

  $ narya stream.ny -e "def s_eq_s' : Id (Stream A) s s' := refl s"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def s_eq_s' : Id (Stream A) s s' := refl s
     ^ term synthesized type
         Stream⁽ᵉ⁾ A⁽ᵉ⁾ s s
       but is being checked against type
         Stream⁽ᵉ⁾ A⁽ᵉ⁾ s s'
       unequal head constants:
         s
       does not equal
         s'
  
  [1]
  $ narya stream.ny -e "def s_eq_s'' : Id (Stream A) s s'' := refl s"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def s_eq_s'' : Id (Stream A) s s'' := refl s
     ^ term synthesized type
         Stream⁽ᵉ⁾ A⁽ᵉ⁾ s s
       but is being checked against type
         Stream⁽ᵉ⁾ A⁽ᵉ⁾ s (corec A (Stream A) (x ↦ x .head) (x ↦ x .tail) s)
       unequal head constants:
         s
       does not equal
         corec
  
  [1]
  $ narya stream.ny -e "def ∞eta_bisim' : Id (Stream A → Stream A) (s ↦ s) (s ↦ ∞eta s) ≔ refl (s ↦ ∞eta s)"
   ￫ error[E0400]
   ￭ command-line exec string
   1 | def ∞eta_bisim' : Id (Stream A → Stream A) (s ↦ s) (s ↦ ∞eta s) ≔ refl (s ↦ ∞eta s)
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]

