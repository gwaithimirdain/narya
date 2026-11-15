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

In a match, an implicit argument of a constructor can be omitted from a pattern, in which case it is bound by a variable that the user can't refer to, or bound by a variable in braces.  Braced patterns fill the implicit arguments from the left, so "{_}" skips one, and they can be deep patterns.  When displayed, an omitted implicit argument, or one bound by "{_}", appears in braces only if the body of the branch mentions it, or if displaying implicits.

  $ narya - <<EOF
  > import "vec"
  > def len (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x xs ↦ suc. (len _ xs) ]
  > def len2 (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. {k} x xs ↦ suc. k ]
  > def len3 (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. {_} x xs ↦ zero. ]
  > def deep (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. {zero.} x xs ↦ zero. | cons. {suc. k} x xs ↦ k ]
  > def map (f : A → A) (n : ℕ) (v : Vec n) : Vec n ≔ match v [ nil. ↦ nil. | cons. x xs ↦ cons. (f x) (map f _ xs) ]
  > def nested (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x (cons. {k} y ys) ↦ k | cons. x nil. ↦ zero. ]
  > def abs : (n : ℕ) (v : Vec n) → ℕ ≔ [ m, nil. ↦ zero. | m, cons. {k} x xs ↦ k ]
  > def const (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x xs ↦ zero. ]
  > about len
  > about len2
  > about len3
  > about deep
  > about map
  > about nested
  > about abs
  > about const
  > display implicits ≔ on
  > about const
  > about map
  > EOF
  n v ↦ match v [ cons. {n′} x xs ↦ suc. (len n′ xs) | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  n v ↦ match v [ cons. {k} x xs ↦ suc. k | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  n v ↦ match v [ cons. x xs ↦ 0 | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  n v ↦
  match v [
  | cons. {n′} x xs ↦ match n′ [ suc. k ↦ k | zero. ↦ 0 ]
  | nil. ↦ 0]
    : (n : ℕ) (v : Vec n) → ℕ
  
  f n v ↦
  match v [ cons. {n′} x xs ↦ cons. (f x) (map f n′ xs) | nil. ↦ nil. ]
    : (f : A → A) (n : ℕ) (v : Vec n) → Vec n
  
  n v ↦
  match v [
  | cons. x xs ↦ match xs [ cons. {k} y ys ↦ k | nil. ↦ 0 ]
  | nil. ↦ 0]
    : (n : ℕ) (v : Vec n) → ℕ
  
  𝑥 𝑦 ↦ match 𝑦 [ cons. {k} x xs ↦ k | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  n v ↦ match v [ cons. x xs ↦ 0 | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  n v ↦ match v [ cons. {n′} x xs ↦ 0 | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  f n v ↦
  match v [ cons. {n′} x xs ↦ cons. {n′} (f x) (map f n′ xs) | nil. ↦ nil. ]
    : (f : A → A) (n : ℕ) (v : Vec n) → Vec n
  

An omitted implicit argument is still in the context of a hole, and other entries can mention it, so it is displayed there, but marked as not in scope, since the user can't refer to it.

  $ narya vec.ny -v -e 'def f (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x xs ↦ ? ]' 2>&1 | grep -A8 'hole ?0'
   ￮ hole ?0:
     
     n′ : ℕ (not in scope)
     n ≔ suc. n′ : ℕ
     x : A
     xs : Vec n′
     v ≔ cons. x xs : Vec (suc. n′)
     ----------------------------------------------------------------------
     ℕ

Errors in patterns.

  $ narya vec.ny -e 'def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x ↦ zero. ]'
   ￫ error[E1303]
   ￭ command-line exec string
   1 | def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x ↦ zero. ]
     ^ not enough arguments to constructor cons in match pattern (need 1 more)
  
  [1]
  $ narya vec.ny -e 'def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x xs y ↦ zero. ]'
   ￫ error[E1303]
   ￭ command-line exec string
   1 | def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x xs y ↦ zero. ]
     ^ too many arguments to constructor cons in match pattern (1 extra)
  
  [1]
  $ narya vec.ny -e 'def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x xs {k} ↦ zero. ]'
   ￫ error[E1303]
   ￭ command-line exec string
   1 | def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. x xs {k} ↦ zero. ]
     ^ too many arguments to constructor cons in match pattern (1 extra)
  
  [1]
  $ narya vec.ny -e 'def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. {k} {y} x xs ↦ zero. ]'
   ￫ error[E1310]
   ￭ command-line exec string
   1 | def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. {k} {y} x xs ↦ zero. ]
     ^ too many boundary arguments for higher-dimensional pattern variable (1 extra)
  
  [1]

All the branches for one constructor must put the same arguments in braces.

  $ narya vec.ny -e 'def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. {zero.} x xs ↦ zero. | cons. x (cons. y ys) ↦ zero. | cons. x nil. ↦ zero. ]'
   ￫ error[E1306]
   ￭ command-line exec string
   1 | def e (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. {zero.} x xs ↦ zero. | cons. x (cons. y ys) ↦ zero. | cons. x nil. ↦ zero. ]
     ^ inconsistent patterns in match
  
  [1]

In a higher-dimensional match with the cube abstraction ⤇, a braced implicit argument is a cube variable, and an omitted one is bound invisibly.

  $ narya vec.ny -v -e "def h (n0 n1 : ℕ) (n2 : Id ℕ n0 n1) (v0 : Vec n0) (v1 : Vec n1) (v2 : Vec⁽ᵉ⁾ n2 v0 v1) : Id ℕ n0 n1 ≔ match v2 [ nil. ⤇ refl zero. | cons. {k} x xs ⤇ suc. k.2 ]" -e 'about h' -e "def h' (n0 n1 : ℕ) (n2 : Id ℕ n0 n1) (v0 : Vec n0) (v1 : Vec n1) (v2 : Vec⁽ᵉ⁾ n2 v0 v1) : Id ℕ n0 n1 ≔ match v2 [ nil. ⤇ refl zero. | cons. x xs ⤇ ? ]" 2>&1 | grep -v 'I0001\|assumed\|^ *$'
   ￫ info[I0000]
   ￮ constant ℕ defined
   ￫ info[I0000]
   ￮ constant Vec defined
   ￫ info[I0000]
   ￮ constant Vec' defined
   ￫ info[I0000]
   ￮ constant h defined
  n0 n1 n2 v0 v1 v2 ↦ match v2 [ cons. {k} x xs ⤇ suc. k.2 | nil. ⤇ refl 0 ]
    : (n0 : ℕ) (n1 : ℕ) (n2 : ℕ⁽ᵉ⁾ n0 n1) (v0 : Vec n0) (v1 : Vec n1)
      (v2 : Vec⁽ᵉ⁾ n2 v0 v1)
      → ℕ⁽ᵉ⁾ n0 n1
   ￫ info[I0000]
   ￮ constant h' defined, containing 1 hole
   ￫ info[I3003]
   ￮ hole ?0:
     n.0 : ℕ (not in scope)
     n.1 : ℕ (not in scope)
     n.2 : ℕ⁽ᵉ⁾ n.0 n.1 (not in scope)
     n0 ≔ suc. n.0 : ℕ
     n1 ≔ suc. n.1 : ℕ
     n2 ≔ suc. n.2 : ℕ⁽ᵉ⁾ (suc. n.0) (suc. n.1)
     x.0 : A
     x.1 : A
     x.2 : Id A x.0 x.1
     xs.0 : Vec n.0
     xs.1 : Vec n.1
     xs.2 : Vec⁽ᵉ⁾ n.2 xs.0 xs.1
     v0 ≔ cons. x.0 xs.0 : Vec (suc. n.0)
     v1 ≔ cons. x.1 xs.1 : Vec (suc. n.1)
     v2 ≔ cons. x.2 xs.2
       : Vec⁽ᵉ⁾ {suc. n.0} {suc. n.1} (suc. n.2) (cons. x.0 xs.0) (cons. x.1 xs.1)
     ----------------------------------------------------------------------
     ℕ⁽ᵉ⁾ (suc. n.0) (suc. n.1)
   ￫ error[E3002]
   ￮ command-line exec string contains open holes

In a higher-dimensional match with the non-cube abstraction ↦, every variable is named face by face, so an implicit argument must have all its faces in braces, and can't be omitted.

  $ narya vec.ny -e "def h (n0 n1 : ℕ) (n2 : Id ℕ n0 n1) (v0 : Vec n0) (v1 : Vec n1) (v2 : Vec⁽ᵉ⁾ n2 v0 v1) : Id ℕ n0 n1 ≔ match v2 [ nil. ↦ refl zero. | cons. {k0} {k1} {k2} {x0} {x1} x2 {xs0} {xs1} xs2 ↦ suc. k2 ]" -e 'about h'
  n0 n1 n2 v0 v1 v2 ↦
  match v2 [
  | cons. {k0} {k1} {k2} {x0} {x1} x2 {xs0} {xs1} xs2 ↦ suc. k2
  | nil. ↦ refl 0]
    : (n0 : ℕ) (n1 : ℕ) (n2 : ℕ⁽ᵉ⁾ n0 n1) (v0 : Vec n0) (v1 : Vec n1)
      (v2 : Vec⁽ᵉ⁾ n2 v0 v1)
      → ℕ⁽ᵉ⁾ n0 n1
  

  $ narya vec.ny -e "def h (n0 n1 : ℕ) (n2 : Id ℕ n0 n1) (v0 : Vec n0) (v1 : Vec n1) (v2 : Vec⁽ᵉ⁾ n2 v0 v1) : Id ℕ n0 n1 ≔ match v2 [ nil. ↦ refl zero. | cons. {x0} {x1} x2 {xs0} {xs1} xs2 ↦ n2 ]"
   ￫ error[E0510]
   ￭ command-line exec string
   1 | def h (n0 n1 : ℕ) (n2 : Id ℕ n0 n1) (v0 : Vec n0) (v1 : Vec n1) (v2 : Vec⁽ᵉ⁾ n2 v0 v1) : Id ℕ n0 n1 ≔ match v2 [ nil. ↦ refl zero. | cons. {x0} {x1} x2 {xs0} {xs1} xs2 ↦ n2 ]
     ^ e-dimensional match requires cube abstraction
  
   ￫ error[E1310]
   ￭ command-line exec string
   1 | def h (n0 n1 : ℕ) (n2 : Id ℕ n0 n1) (v0 : Vec n0) (v1 : Vec n1) (v2 : Vec⁽ᵉ⁾ n2 v0 v1) : Id ℕ n0 n1 ≔ match v2 [ nil. ↦ refl zero. | cons. {x0} {x1} x2 {xs0} {xs1} xs2 ↦ n2 ]
     ^ not enough boundary arguments for higher-dimensional pattern variable (need 1 more)
  
  [1]

  $ narya vec.ny -e "def h (n0 n1 : ℕ) (n2 : Id ℕ n0 n1) (v0 : Vec n0) (v1 : Vec n1) (v2 : Vec⁽ᵉ⁾ n2 v0 v1) : Id ℕ n0 n1 ≔ match v2 [ nil. ↦ refl zero. | cons. {k} {x0} {x1} x2 {xs0} {xs1} xs2 ↦ n2 ]"
   ￫ error[E0510]
   ￭ command-line exec string
   1 | def h (n0 n1 : ℕ) (n2 : Id ℕ n0 n1) (v0 : Vec n0) (v1 : Vec n1) (v2 : Vec⁽ᵉ⁾ n2 v0 v1) : Id ℕ n0 n1 ≔ match v2 [ nil. ↦ refl zero. | cons. {k} {x0} {x1} x2 {xs0} {xs1} xs2 ↦ n2 ]
     ^ e-dimensional match requires cube abstraction
  
  [1]

A placeholder in braces in the definition of a notation for a constructor only matches an implicit argument, so it applies only to a constructor that has one there, in terms, patterns, and display.  In display, it can only omit an argument that isn't being displayed.

  $ narya - <<EOF
  > import "vec"
  > def L : Type ≔ data [ nil. | cons. (x : A) (xs : L) ]
  > notation(5) x "∷" xs ≔ cons. {_} x xs
  > def v : Vec 1 ≔ a ∷ nil.
  > echo v
  > echo (cons. a nil. : L)
  > def f (n : ℕ) (v : Vec n) : A ≔ match v [ nil. ↦ a | x ∷ xs ↦ x ]
  > def g (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | cons. {k} x xs ↦ k ]
  > about f
  > about g
  > display implicits ≔ on
  > echo v
  > def l : L ≔ a ∷ nil.
  > EOF
  a ∷ nil.
    : Vec 1
  
  cons. a nil.
    : L
  
  n v ↦ match v [ x ∷ xs ↦ x | nil. ↦ a ]
    : (n : ℕ) (v : Vec n) → A
  
  n v ↦ match v [ cons. {k} x xs ↦ k | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  cons. {0} a nil.
    : Vec 1
  
   ￫ error[E0702]
   ￭ stdin
   13 | def l : L ≔ a ∷ nil.
      ^ unexpected implicit argument: expecting explicit primary argument of constructor cons
  
  [1]

Notations for constructors can mention implicit arguments, which match implicit arguments in display.

  $ narya - <<EOF
  > import "vec"
  > notation(5) x "∷" xs ≔ cons. x xs
  > notation(5) x "⊲" n "⊳" xs ≔ cons. {n} x xs
  > def v : Vec 2 ≔ a ∷ (a ∷ nil.)
  > def w : Vec 2 ≔ a ⊲ 1 ⊳ (a ⊲ 0 ⊳ nil.)
  > echo v
  > echo w
  > def f (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | x ∷ xs ↦ zero. ]
  > def g (n : ℕ) (v : Vec n) : ℕ ≔ match v [ nil. ↦ zero. | x ⊲ k ⊳ xs ↦ k ]
  > def h (n : ℕ) (v : Vec n) : Vec n ≔ match v [ nil. ↦ nil. | cons. x xs ↦ cons. x xs ]
  > about f
  > about g
  > about h
  > display implicits ≔ on
  > echo v
  > EOF
  a ∷ (a ∷ nil.)
    : Vec 2
  
  a ∷ (a ∷ nil.)
    : Vec 2
  
  n v ↦ match v [ x ∷ xs ↦ 0 | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  n v ↦ match v [ x ⊲ k ⊳ xs ↦ k | nil. ↦ 0 ]
    : (n : ℕ) (v : Vec n) → ℕ
  
  n v ↦ match v [ x ∷ xs ↦ x ∷ xs | nil. ↦ nil. ]
    : (n : ℕ) (v : Vec n) → Vec n
  
  a ⊲ 1 ⊳ (a ⊲ 0 ⊳ nil.)
    : Vec 2
  

The "split" command omits the implicit arguments of constructors.

  $ narya vec.ny -fake-interact 'def f (n : ℕ) (v : Vec n) : ℕ ≔ ? split 0 ≔ v def S : Type ≔ data [ s. {n : ℕ} (x : A) ] def g : S ≔ ? split 1 ≔ _' 2>&1 | grep -A1 'split successful'
   ￮ split successful, hole could be solved by:
       match v [ nil. ↦ ? | cons. x xs ↦ ? ]
  --
   ￮ split successful, hole could be solved by:
       s. ?
