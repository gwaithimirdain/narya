  $ cat >wrap.ny <<EOF
  > axiom A:Type
  > axiom a:A
  > def wrapA : Type := sig ( unwrap : A)
  > def wa1 : wrapA := (unwrap := a)
  > def wa2 : wrapA := (_ := a)
  > def wa3 : wrapA := (a,)
  > def wa4 : wrapA := (a)
  > EOF

  $ narya -v wrap.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant wrapA defined
  
   ￫ info[I0000]
   ￮ constant wa1 defined
  
   ￫ info[I0000]
   ￮ constant wa2 defined
  
   ￫ info[I0000]
   ￮ constant wa3 defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/wrap.ny
   7 | def wa4 : wrapA := (a)
     ^ term synthesized type
         A
       but is being checked against type
         wrapA
       unequal head constants:
         A
       does not equal
         wrapA
  
  [1]
