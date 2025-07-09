  $ narya -v issue69.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0000]
   ￮ constant D defined
  
   ￫ info[I0000]
   ￮ constant get_a defined
  
   ￫ info[I0000]
   ￮ constant get_f defined
  

  $ narya -v match_in_type.ny
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/match_in_type.ny
   3 | def test (m : ⊤) : match m [ star. ↦ sig () ] ≔ ?
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant test defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     m : ⊤
     ----------------------------------------------------------------------
     _match.0{…}
  
   ￫ error[E3002]
   ￮ file match_in_type.ny contains open holes
  
  [1]
