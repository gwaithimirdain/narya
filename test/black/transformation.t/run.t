  $ narya -v -transformation transformation.ny
   ￫ info[I0000]
   ￮ constant ○ defined
  
   ￫ info[I0000]
   ￮ constant ▱ defined
  
   ￫ info[I0000]
   ￮ constant induced defined
  


The 2-cell alpha only goes from ○ to ▱, not the other way, so there is no induced function ▱ A → ○ A.

  $ narya -transformation transformation.ny -e "def backwards (A :▱| DomMode) (u : ▱ A) : ○ A := match u [ box. x ↦ circle. x ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def backwards (A :▱| DomMode) (u : ▱ A) : ○ A := match u [ box. x ↦ circle. x ]
     ^ use of ▱ variable behind ○ lock requires a key
  
  [1]

