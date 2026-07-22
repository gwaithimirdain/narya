  $ narya -v -composable-transformations composable_transformations.ny
   ￫ info[I0000]
   ￮ constant ○ defined
  
   ￫ info[I0000]
   ￮ constant ▱ defined
  
   ￫ info[I0000]
   ￮ constant ▹ defined
  
   ￫ info[I0000]
   ￮ constant alpha_map defined
  
   ￫ info[I0000]
   ￮ constant beta_map defined
  
   ￫ info[I0000]
   ￮ constant gamma_map defined
  
   ￫ info[I0000]
   ￮ constant composed defined
  
   ￫ info[I0000]
   ￮ constant composed_ok defined
  


There is no 2-cell in the reverse direction, so there is no induced function ▹ A → ○ A.

  $ narya -composable-transformations composable_transformations.ny -e "def backwards (A :▹| DomMode) (u : ▹ A) : ○ A := match u [ tri. x ↦ circle. x ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def backwards (A :▹| DomMode) (u : ▹ A) : ○ A := match u [ tri. x ↦ circle. x ]
     ^ use of ▹ variable behind ○ lock requires a key
  
  [1]


