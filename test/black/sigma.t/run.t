  $ narya -v sigma.ny
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0000]
   ￮ constant pair defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0000]
   ￮ constant ab defined
  
   ￫ info[I0000]
   ￮ constant ab' defined
  
   ￫ info[I0000]
   ￮ constant ab_equals_ab' defined
  
   ￫ info[I0001]
   ￮ axiom x assumed
  
   ￫ info[I0000]
   ￮ constant x1 defined
  
   ￫ info[I0000]
   ￮ constant x2 defined
  
   ￫ info[I0000]
   ￮ constant ab_fst_equals_a defined
  
   ￫ info[I0000]
   ￮ constant ab_snd_equals_b defined
  
   ￫ info[I0000]
   ￮ constant ab'_fst_equals_a defined
  
   ￫ info[I0000]
   ￮ constant ab'_snd_equals_b defined
  
   ￫ info[I0000]
   ￮ constant x' defined
  
   ￫ info[I0000]
   ￮ constant x_equals_x' defined
  
   ￫ info[I0000]
   ￮ constant x'' defined
  
   ￫ info[I0000]
   ￮ constant x_equals_x'' defined
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0001]
   ￮ axiom b0 assumed
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0001]
   ￮ axiom b1 assumed
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  
   ￫ info[I0001]
   ￮ axiom b2 assumed
  
   ￫ info[I0000]
   ￮ constant ab2 defined
  
   ￫ info[I0000]
   ￮ constant invariance1 defined
  
   ￫ info[I0000]
   ￮ constant invariance2 defined
  
   ￫ info[I0000]
   ￮ constant ab2_fst_equals_a2 defined
  
   ￫ info[I0000]
   ￮ constant ab2_snd_equals_b2 defined
  
   ￫ info[I0000]
   ￮ constant refl_comm1 defined
  
   ￫ info[I0000]
   ￮ constant refl_comm2 defined
  
   ￫ info[I0001]
   ￮ axiom X assumed
  
   ￫ info[I0001]
   ￮ axiom x00 assumed
  
   ￫ info[I0001]
   ￮ axiom x01 assumed
  
   ￫ info[I0001]
   ￮ axiom x02 assumed
  
   ￫ info[I0001]
   ￮ axiom x10 assumed
  
   ￫ info[I0001]
   ￮ axiom x11 assumed
  
   ￫ info[I0001]
   ￮ axiom x12 assumed
  
   ￫ info[I0001]
   ￮ axiom x20 assumed
  
   ￫ info[I0001]
   ￮ axiom x21 assumed
  
   ￫ info[I0001]
   ￮ axiom x22 assumed
  
   ￫ info[I0001]
   ￮ axiom Y assumed
  
   ￫ info[I0001]
   ￮ axiom y assumed
  
   ￫ info[I0001]
   ￮ axiom s assumed
  
   ￫ info[I0000]
   ￮ constant s1s defined
  
  $ narya sigma.ny -e "echo (sym s)"
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo (sym s)
     ^ argument of degeneracy 'sym' must have dimension at least ee
  
  [1]
