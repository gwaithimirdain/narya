Constructors can take implicit arguments, declared in braces, either as parameters or in a function-type.  Which arguments are implicit is determined by the datatype that a constructor is checked against.

  $ cat >vec.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > axiom A : Type
  > axiom a : A
  > axiom a' : A
  > axiom q : Id A a a'
  > def Vec : ℕ → Type ≔ data [
  > | nil. : Vec zero.
  > | cons. {n : ℕ} (x : A) (xs : Vec n) : Vec (suc. n) ]
  > def Vec' : ℕ → Type ≔ data [
  > | nil. : Vec' zero.
  > | cons. : {n : ℕ} → A → Vec' n → Vec' (suc. n) ]
  > EOF

Implicit arguments are inserted wherever they are missing, including at the end, since a constructor is always fully applied.  They can be given explicitly in braces, and are displayed only when displaying implicits.

  $ narya - <<EOF
  > import "vec"
  > def v1 : Vec 1 ≔ cons. {0} a nil.
  > def v2 : Vec 2 ≔ cons. a (cons. a nil.)
  > def v3 : Vec 2 ≔ cons. {_} a v1
  > def w2 : Vec' 2 ≔ cons. a (cons. a nil.)
  > echo v2
  > echo w2
  > display implicits ≔ on
  > echo v2
  > display implicits ≔ off
  > def T : Type ≔ data [ t. (x : A) {y : A} ]
  > def t2 : T ≔ t. a {a}
  > echo t2
  > EOF
  cons. a (cons. a nil.)
    : Vec 2
  
  cons. a (cons. a nil.)
    : Vec' 2
  
  cons. {1} a (cons. {0} a nil.)
    : Vec 2
  
  t. a
    : T
  

A datatype is displayed with the braces.

  $ narya vec.ny -e 'echo (data [ t. {x : A} (y : A) | u. {x : A} (_ : A) {z : A} ] : Type)'
  data #(gen) [
  | t. {x : A} (y : A)
  | u. {x : A} (𝑥 : A) {z : A} ]
    : Type
  

An implicit argument that can't be determined is an error at the constructor.

  $ narya vec.ny -e 'def T : Type ≔ data [ t. (x : A) {y : A} ]' -e 'def t1 : T ≔ t. a'
   ￫ error[E2005]
   ￭ command-line exec string
   1 | def t1 : T ≔ t. a
     ^ can't determine implicit argument y of t.
  
  [1]

  $ narya vec.ny -e 'def T : Type ≔ data [ t. (x : A) {y : A} ]' -e 'def t2 : T ≔ t. a {a} a'
   ￫ error[E1001]
   ￭ command-line exec string
   1 | def t2 : T ≔ t. a {a} a
     ^ too many arguments to constructor t (1 extra)
  
  [1]

  $ narya vec.ny -e 'def v : Vec 1 ≔ cons. {0} {a} nil.'
   ￫ error[E0702]
   ￭ command-line exec string
   1 | def v : Vec 1 ≔ cons. {0} {a} nil.
     ^ unexpected implicit argument: expecting explicit primary argument of constructor cons
  
  [1]

A constructor at a function-type is eta-expanded, with the implicitness of the function-type.

  $ narya vec.ny -e 'def T : Type ≔ data [ t. (x : A) {y : A} ]' -e 'def f : {y : A} → T ≔ t. a' -e 'echo f {a}' -e 'def g : A → Vec 1 ≔ x ↦ cons. x nil.'
  t. a
    : T
  

In a higher-dimensional instance of a constructor, the braced arguments supply the faces of the cube of an implicit argument in order, or labelled by the face they supply, as in a function application.  The boundary faces are determined by the type, so they are only documentation, and a dot ends the cube.

  $ narya - <<EOF
  > import "vec"
  > def v1 : Vec 1 ≔ cons. a nil.
  > def v1' : Vec 1 ≔ cons. a' nil.
  > def p : Id (Vec 1) v1 v1' ≔ cons. q nil.
  > def p2 : Id (Vec 1) v1 v1' ≔ cons. {0} {0} {zero.} {a} {a'} q nil.
  > def p3 : Id (Vec 1) v1 v1' ≔ cons. {2 ≔ zero.} q nil.
  > def p4 : Id (Vec 1) v1 v1' ≔ cons. {0 ≔ 0} . {a} q nil.
  > def p5 : Id (Vec 1) v1 v1' ≔ cons. {1 ≔ 0} . {1 ≔ a'} q nil.
  > echo p
  > display implicits ≔ on
  > echo p
  > EOF
  cons. q nil.
    : Vec⁽ᵉ⁾ {1} {1} (refl 1) (cons. a nil.) (cons. a' nil.)
  
  cons. {0} {0} {refl 0} {a} {a'} q {nil.} {nil.} nil.
    : Vec⁽ᵉ⁾ {1} {1} (refl 1) (cons. {0} a nil.) (cons. {0} a' nil.)
  

  $ narya vec.ny -e "def v1 : Vec 1 ≔ cons. a nil." -e "def v1' : Vec 1 ≔ cons. a' nil." -e "def p : Id (Vec 1) v1 v1' ≔ cons. {1 ≔ 0} {0 ≔ 0} q nil."
   ￫ error[E0712]
   ￭ command-line exec string
   1 | def p : Id (Vec 1) v1 v1' ≔ cons. {1 ≔ 0} {0 ≔ 0} q nil.
     ^ invalid face argument: face 0 is out of order or repeated: faces must be given in order, and a dot starts the next cube
  
  [1]

  $ narya vec.ny -e "def v1 : Vec 1 ≔ cons. a nil." -e "def v1' : Vec 1 ≔ cons. a' nil." -e "def p : Id (Vec 1) v1 v1' ≔ cons. {0} {1} q nil."
   ￫ error[E1004]
   ￭ command-line exec string
   1 | def p : Id (Vec 1) v1 v1' ≔ cons. {0} {1} q nil.
     ^ supplied 1-boundary argument
         1
       doesn't match the one determined by the type
         0
       unequal constructors:
         suc
       does not equal
         zero
  
  [1]

  $ narya vec.ny -e "def v1 : Vec 1 ≔ cons. a nil." -e "def v1' : Vec 1 ≔ cons. a' nil." -e "def p : Id (Vec 1) v1 v1' ≔ cons. {0 ≔ 0} . . q nil."
   ￫ error[E0712]
   ￭ command-line exec string
   1 | def p : Id (Vec 1) v1 v1' ≔ cons. {0 ≔ 0} . . q nil.
     ^ invalid face argument: a dot can't supply the primary argument of an explicit argument of a constructor
  
  [1]

Braces in constructor declarations are preserved by reformatting.

  $ cat >rf.ny <<EOF
  > axiom A : Type
  > def T : Type ≔ data [ t.  {x:A} (y : A) | u. : {x : A} →  A → T ]
  > EOF
  $ narya rf.ny
  $ cat rf.ny
  axiom A : Type
  
  def T : Type ≔ data [ t. {x : A} (y : A) | u. : {x : A} → A → T ]
