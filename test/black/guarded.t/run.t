  $ narya -v -guarded guarded.ny
   ￫ info[I0000]
   ￮ constant ▹ defined
  
   ￫ info[I0000]
   ￮ constant eta defined
  
   ￫ info[I0000]
   ￮ constant eta2 defined
  
   ￫ info[I0000]
   ￮ constant □ defined
  
   ￫ info[I0000]
   ￮ constant box defined
  
   ￫ info[I0000]
   ￮ constant unbox defined
  
   ￫ info[I0000]
   ￮ constant box_from_later defined
  
   ￫ info[I0000]
   ￮ constant box_later_from_box defined
  


There is no cell in the reverse direction of next, so a ▹-locked value cannot be used directly.

  $ narya -guarded guarded.ny -e "def backwards (A : Type) (x :▹| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def backwards (A : Type) (x :▹| A) : A := x
     ^ use of ▹ variable behind id lock requires a key
  
  [1]


Nor is there a cell going from more laters to fewer.

  $ narya -guarded guarded.ny -e "def backwards2 (A :▹| Type) (x :▹▹| A) : ▹ A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def backwards2 (A :▹| Type) (x :▹▹| A) : ▹ A := x
     ^ use of ▹▹ variable behind id lock requires a key
  
  [1]


