Defining a constant or axiom with the same name as a mode (e.g. "Type" in the trivial mode theory) should be rejected.

  $ narya -e 'axiom Type : Type'
   ￫ error[E2101]
   ￮ invalid constant name: Type (that's a mode name)
  
  [1]


  $ narya -e 'def Type : Type := Type'
   ￫ error[E2101]
   ￮ invalid constant name: Type (that's a mode name)
  
  [1]


An ordinary name is unaffected.

  $ narya -v -e 'axiom foo : Type'
   ￫ info[I0001]
   ￮ axiom foo assumed
  

