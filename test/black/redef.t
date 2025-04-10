  $ cat >one.ny <<EOF
  > def A : Type ≔ Type
  > EOF

  $ cat >two.ny <<EOF
  > import "one"
  > def A : Type ≔ sig ()
  > EOF

  $ narya -v two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0000]
   ￮ constant A defined
  

  $ cat >three.ny <<EOF
  > export "one"
  > def A : Type ≔ sig ()
  > EOF

  $ narya -v three.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (compiled)
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/three.ny
   2 | def A : Type ≔ sig ()
     ^ redefining constant: A
   ￭ $TESTCASE_ROOT/one.ny
   1 | def A : Type ≔ Type
     ^ previous definition
  
   ￫ info[I0000]
   ￮ constant A defined
  

  $ cat >oneone.ny <<EOF
  > def A : Type ≔ Type
  > def A : Type ≔ sig ()
  > EOF

  $ narya oneone.ny
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/oneone.ny
   1 | def A : Type ≔ Type
     ^ previous definition
   2 | def A : Type ≔ sig ()
     ^ redefining constant: A
  

  $ cat >onesect.ny <<EOF
  > def A : Type ≔ Type
  > section foo ≔
  >   def A : Type ≔ sig ()
  >   def B : Type := data []
  >   def C : Type := data [ one. ]
  > end
  > import foo
  > def B : Type := codata []
  > export foo
  > def C : Type := sig ( one : Type )
  > EOF

  $ narya -v onesect.ny
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0007]
   ￮ section foo opened
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0000]
   ￮ constant B defined
  
   ￫ info[I0000]
   ￮ constant C defined
  
   ￫ info[I0008]
   ￮ section foo closed
  
   ￫ info[I0000]
   ￮ constant B defined
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/onesect.ny
    5 |   def C : Type := data [ one. ]
      ^ previous definition
    6 | end
    7 | import foo
    8 | def B : Type := codata []
    9 | export foo
   10 | def C : Type := sig ( one : Type )
      ^ redefining constant: C
  
   ￫ info[I0000]
   ￮ constant C defined
  
