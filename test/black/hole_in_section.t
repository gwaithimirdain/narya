  $ narya -fake-interact "section foo ≔ def A : Type ≔ sig () def B : A ≔ ? def C : A ≔ ? end show hole 0 show hole 1"
   ￫ info[I0007]
   ￮ section foo opened
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0000]
   ￮ constant B defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     A
  
   ￫ info[I0000]
   ￮ constant C defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     A
  
   ￫ info[I0008]
   ￮ section foo closed
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     A
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     A
  
