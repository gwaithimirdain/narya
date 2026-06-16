A codatatype can't have a lower field and a higher field with the same name.

  $ narya lowhigh.ny
   ￫ error[E1507]
   ￭ $TESTCASE_ROOT/lowhigh.ny
   3 | def foo : Type ≔ codata [
   4 | | x .f : A
   5 | | x .f.e : A → A ]
     ^ codatatype has both lower and higher methods named 'f'
  
  [1]

  $ narya highlow.ny
   ￫ error[E1507]
   ￭ $TESTCASE_ROOT/highlow.ny
   3 | def foo : Type ≔ codata [
   4 | | x .f.e : A → A
   5 | | x .f : A ]
     ^ codatatype has both lower and higher methods named 'f'
  
  [1]
