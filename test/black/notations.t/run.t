  $ narya -v constrs.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant twos defined
  
   ￫ info[I0002]
   ￮ notation twos.foo defined
  
   ￫ info[I0000]
   ￮ constant threes defined
  
   ￫ info[I0002]
   ￮ notation threes.foo defined
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant a2 defined
  
  a + a
    : twos
  
   ￫ info[I0000]
   ￮ constant a3 defined
  
  a * a * a
    : threes
  
  $ narya minus.ny
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  4
    : ℤ
  
  negsuc. 3
    : ℤ
  
  0
    : ℤ
  
  0
    : ℤ
  

  $ narya -v subminusminus.ny
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/minus.nyo
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/minus.ny (compiled)
  
   ￫ info[I0002]
   ￮ notation sub defined
  
   ￫ info[I0002]
   ￮ notation minus defined
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  0
    : ℤ
  
  0
    : ℤ
  
   ￫ warning[E2209]
   ￮ replacing printing notation for ℤ.minus (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation minus' defined
  
  2
    : ℤ
  
   ￫ error[E0201]
   ￮ potential ambiguity (one notation is a prefix of another). Notations involved:
       minus
       minus'
  
  [1]

  $ narya -v minussubminus.ny
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/minus.nyo
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/minus.ny (compiled)
  
   ￫ info[I0002]
   ￮ notation minus defined
  
   ￫ info[I0002]
   ￮ notation sub defined
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  0
    : ℤ
  
  0
    : ℤ
  
   ￫ warning[E2209]
   ￮ replacing printing notation for ℤ.minus (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation minus' defined
  
  2
    : ℤ
  
   ￫ error[E0201]
   ￮ potential ambiguity (one notation is a prefix of another). Notations involved:
       minus
       minus'
  
  [1]

  $ narya -v minusminussub.ny
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/minus.nyo
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/minus.ny (compiled)
  
   ￫ info[I0002]
   ￮ notation minus defined
  
   ￫ warning[E2209]
   ￮ replacing printing notation for ℤ.minus (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation minus' defined
  
   ￫ info[I0002]
   ￮ notation sub defined
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
   ￫ error[E0201]
   ￮ potential ambiguity (one notation is a prefix of another). Notations involved:
       minus
       minus'
  
  [1]
