  $ narya -v -idempotent-comonad box.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant □ defined
  
   ￫ info[I0000]
   ￮ constant □map defined
  
   ￫ info[I0000]
   ￮ constant ε defined
  
   ￫ info[I0000]
   ￮ constant △ defined
  
   ￫ info[I0000]
   ￮ constant □ε∘△ defined
  
   ￫ info[I0000]
   ￮ constant ε□∘△ defined
  

  $ narya -idempotent-comonad box.ny -e "def g (A : Type) (x : A) : A := f A x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def g (A : Type) (x : A) : A := f A x
     ^ use of id variable behind □ lock requires a key
  
  [1]

  $ narya -idempotent-comonad box.ny -e "def η (A :□| Type) (x : A) : □ A := box. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def η (A :□| Type) (x : A) : □ A := box. x
     ^ use of id variable behind □ lock requires a key
  
  [1]
