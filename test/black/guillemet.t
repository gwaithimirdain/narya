  $ narya -v -e "def «a long name» : Type := sig () def « » : «a long name» := ()"
   ￫ info[I0000]
   ￮ constant «a long name» defined
  
   ￫ info[I0000]
   ￮ constant « » defined
  

  $ narya -v -e "def «nested «guillemets» here» : Type := sig () def «a + b» : «nested «guillemets» here» := ()"
   ￫ info[I0000]
   ￮ constant «nested «guillemets» here» defined
  
   ￫ info[I0000]
   ￮ constant «a + b» defined
  

  $ narya -v -e "def «foo.bar» : Type := sig () import foo def x : bar := ()"
   ￫ info[I0000]
   ￮ constant «foo.bar» defined
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | def «foo.bar» : Type := sig () import foo def x : bar := ()
     ^ unbound variable: bar
  
  [1]

  $ narya -v -e "def «foo.bar» : Type := sig () import «foo def x : bar» := ()"
   ￫ info[I0000]
   ￮ constant «foo.bar» defined
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def «foo.bar» : Type := sig () import «foo def x : bar» := ()
     ^ parse error
  
  [1]

  $ narya -v -e "def «foo.bar» : Type := sig () import «foo def x : bar := ()"
   ￫ info[I0000]
   ￮ constant «foo.bar» defined
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def «foo.bar» : Type := sig () import «foo def x : bar := ()‹EOF›
     ^ parse error
  
  [1]

  $ narya -v -e "def foo.«a long name» : Type := sig () import foo def « » : «a long name» := ()"
   ￫ info[I0000]
   ￮ constant foo.«a long name» defined
  
   ￫ info[I0000]
   ￮ constant « » defined
  

  $ narya -v -e "def «contains \` comments» : Type := sig () import foo def «{\`» : «contains \` comments» := ()"
   ￫ info[I0000]
   ￮ constant «contains ` comments» defined
  
   ￫ info[I0000]
   ￮ constant «{`» defined
  

  $ narya -v -e "def «contains \" quotes» : Type := sig () import foo def «\"» : «contains \" quotes» := ()"
   ￫ info[I0000]
   ￮ constant «contains " quotes» defined
  
   ￫ info[I0000]
   ￮ constant «"» defined
  
