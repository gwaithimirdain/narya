  $ narya -v -coreflector box.ny
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
  

  $ narya -coreflector box.ny -e "def g (A : Type) (x : A) : A := f A x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def g (A : Type) (x : A) : A := f A x
     ^ use of id variable behind □ lock requires a key
  
  [1]

  $ narya -coreflector box.ny -e "def η (A :□| Type) (x : A) : □ A := box. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def η (A :□| Type) (x : A) : □ A := box. x
     ^ use of id variable behind □ lock requires a key
  
  [1]

  $ narya -v -functor functor.ny
   ￫ info[I0000]
   ￮ constant ○ defined
  
   ￫ info[I0000]
   ￮ constant ○map defined
  


  $ narya -v -reflector reflector.ny
   ￫ info[I0000]
   ￮ constant diamond defined
  
   ￫ info[I0000]
   ￮ constant diamondmap defined
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant η defined
  
   ￫ info[I0000]
   ￮ constant ηη defined
  


Unlike the coreflector, the reflector has no counit, so a ◇-locked variable cannot be used directly at its unlocked type.

  $ narya -reflector reflector.ny -e "def ε (A :◇| Type) (x :◇| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def ε (A :◇| Type) (x :◇| A) : A := x
     ^ use of ◇ variable behind id lock requires a key
  
  [1]


  $ narya -v -spatial spatial.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant sharp defined
  
   ￫ info[I0000]
   ￮ constant wsh defined
  
   ￫ info[I0000]
   ￮ constant counit defined
  
   ￫ info[I0000]
   ￮ constant unit defined
  
   ￫ info[I0000]
   ￮ constant wu defined
  


The reflector ♯ has no counit of its own, unlike the coreflector ♭.

  $ narya -spatial spatial.ny -e "def ε (A :♯| Type) (x :♯| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def ε (A :♯| Type) (x :♯| A) : A := x
     ^ use of ♯ variable behind id lock requires a key
  
  [1]


The coreflector ♭ has no unit of its own, unlike the reflector ♯.

  $ narya -spatial spatial.ny -e "def wfl (x : Type) : (data [ flat. (_ :♭| Type) ]) := flat. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def wfl (x : Type) : (data [ flat. (_ :♭| Type) ]) := flat. x
     ^ use of id variable behind ♭ lock requires a key
  
  [1]


The adjunction ♭ ⊣ ♯ only gives cells ♭∘♯ ⇒ id and id ⇒ ♯∘♭, not the other way around.

  $ narya -spatial spatial.ny -e "def nocounit (A :♯ ♭| Type) (x :♯ ♭| A) : A := x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def nocounit (A :♯ ♭| Type) (x :♯ ♭| A) : A := x
     ^ use of ♯ ♭ variable behind id lock requires a key
  
  [1]


  $ narya -spatial spatial.ny -e "def wu2 (x : Type) : (data [ unit2. (_ :♭ ♯| Type) ]) := unit2. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def wu2 (x : Type) : (data [ unit2. (_ :♭ ♯| Type) ]) := unit2. x
     ^ use of id variable behind ♭ ♯ lock requires a key
  
  [1]


