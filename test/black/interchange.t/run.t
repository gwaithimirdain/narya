  $ narya -v -interchange interchange.ny
   ￫ info[I0000]
   ￮ constant ▹ defined
  
   ￫ info[I0000]
   ￮ constant ◃ defined
  
   ￫ info[I0000]
   ￮ constant ▸ defined
  
   ￫ info[I0000]
   ￮ constant ◂ defined
  
   ￫ info[I0000]
   ￮ constant alpha_map defined
  
   ￫ info[I0000]
   ￮ constant beta_map defined
  
   ￫ info[I0000]
   ￮ constant ▸map defined
  
   ￫ info[I0000]
   ￮ constant ◂map defined
  
   ￫ info[I0000]
   ￮ constant route1 defined
  
   ￫ info[I0000]
   ￮ constant route2 defined
  
   ￫ info[I0000]
   ￮ constant interchange_ok defined
  


There is no 2-cell in the reverse direction, so there is no induced function ◃ A → ▹ A.

  $ narya -interchange interchange.ny -e "def backwards (A :◃| AType) (u : ◃ A) : ▹ A := match u [ lt. x ↦ rt. x ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def backwards (A :◃| AType) (u : ◃ A) : ▹ A := match u [ lt. x ↦ rt. x ]
     ^ use of ◃ variable behind ▹ lock requires a key
  
  [1]


