A group of variables in a pi-type sharing a domain, such as "(x y : A)", binds all of them at once.  Their domain is processed and typechecked only once, in the scope outside all of them.  In particular, it can't refer to the earlier variables of the same group.

  $ cat >pi.ny <<EOF
  > axiom A : Type
  > axiom B : Type
  > axiom a : A
  > axiom b : B
  > EOF

  $ narya pi.ny -e 'echo (A y : A) → Type  echo (x y : A) (z : B) → A → B'
  (A′ : A) (y : A) → Type
    : Type
  
  (x : A) (y : A) (z : B) → A → B
    : Type
  

A hole in the shared domain is created only once, and is shared by all the variables.

  $ narya -v pi.ny -fake-interact 'def t : (x y : ?) → Type ≔ ?  solve 0 ≔ A  echo t'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0000]
   ￮ constant t defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     (x : ?0{…}) (y : ?0{…}) → Type
  
   ￫ info[I0005]
   ￮ hole solved
  
  t
    : (x : A) (y : A) → Type
  

The same is true for a modal domain.

  $ narya -v -spatial pi.ny -fake-interact 'def t : (x y :♭| ?) → Type ≔ ?  solve 0 ≔ A  echo t'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0000]
   ￮ constant t defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     (x :♭| ?0{…}) (y :♭| ?0{…}) → Type
  
   ￫ info[I0005]
   ￮ hole solved
  
  t
    : (x :♭| A) (y :♭| A) → Type
  

A datatype constructor whose type is given as a pi-type takes the domains of that pi-type as its arguments, including groups of variables sharing a domain.

  $ narya pi.ny -e 'def D : Type ≔ data [ c. : (x y : A) → D | d. : A → (B → D) | e. : ((x : A) → D) ]  echo (c. a a : D)  echo (d. a b : D)  echo (e. a : D)'
  c. a a
    : D
  
  d. a b
    : D
  
  e. a
    : D
  

When the domain is modal, the domains of the later variables are weakenings of the first one behind the lock, so their definitions are displayed as written.

  $ narya -spatial pi.ny -e 'axiom F : Type → Type  def G (X : Type) : Type ≔ F X  def T (U :♭| Type) : Type ≔ (x y :♭| G U) (v w : U) → U  about T  echo T A  echo refl (T A)'
  U ↦ (x :♭| G U) (y :♭| G U) (v : U) (w : U) → U
    : (U :♭| Type) → Type
  
  (x :♭| F A) (y :♭| F A) (v : A) (w : A) → A
    : Type
  
  (x :♭| Id F (Id A)) (y :♭| Id F (Id A)) (v : Id A) (w : Id A) ⇒ Id A
    : Type⁽ᵉ⁾ ((x :♭| F A) (y :♭| F A) (v : A) (w : A) → A)
        ((x :♭| F A) (y :♭| F A) (v : A) (w : A) → A)
  

The same goes for the parameters of a definition or axiom, and the arguments of a constructor.

  $ narya pi.ny -e 'def t (A y : A) : Type ≔ Type  echo t  axiom u (A y : A) : Type  echo u  def D : Type ≔ data [ c. (A y : A) ]  echo (c. a a : D)'
  t
    : (A′ : A) (y : A) → Type
  
  u
    : (A′ : A) (y : A) → Type
  
  c. a a
    : D
  

  $ narya -v pi.ny -fake-interact 'def t (x y : ?) : Type ≔ Type  solve 0 ≔ A  echo t'
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ info[I0000]
   ￮ constant t defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Type
  
   ￫ info[I0005]
   ￮ hole solved
  
  t
    : (x : A) (y : A) → Type
  

A match on a parameter refines the types of the parameters that share a type depending on it.

  $ cat >vec.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
  > def Vec (A : Type) : ℕ → Type ≔ data [ nil. : Vec A zero. | cons. (n : ℕ) (x : A) (xs : Vec A n) : Vec A (suc. n) ]
  > def f (n : ℕ) (u v : Vec ℕ n) : ℕ ≔ match u [ nil. ↦ ? | cons. k x xs ↦ ? ]
  > EOF

  $ narya -v -fake-interact vec.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant Vec defined
  
   ￫ info[I0000]
   ￮ constant f defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     n ≔ 0 : ℕ
     u ≔ nil. : Vec ℕ 0
     v : Vec ℕ 0
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     k : ℕ
     n ≔ suc. k : ℕ
     v : Vec ℕ (suc. k)
     x : ℕ
     xs : Vec ℕ k
     u ≔ cons. k x xs : Vec ℕ (suc. k)
     ----------------------------------------------------------------------
     ℕ
  

The same goes for the fields of a record type.  Here too the shared type is processed outside the scope of all the fields, so it refers to the constant A rather than the field A.

  $ narya pi.ny -e 'def S : Type ≔ sig (A y : A, z w : B)  def s : S ≔ (a, a, b, b)  echo s .y  echo s .w'
  a
    : A
  
  b
    : B
  

A group of fields can't contain the same field twice.

  $ narya pi.ny -e 'def S : Type ≔ sig (x y : A, z y : B)'
   ￫ error[E1501]
   ￭ command-line exec string
   1 | def S : Type ≔ sig (x y : A, z y : B)
     ^ duplicate field in record type: y
  
  [1]

If the shared type fails to typecheck, the error is reported only once.

  $ narya pi.ny -e 'def S : Type ≔ sig (x y : a, z : b)'
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def S : Type ≔ sig (x y : a, z : b)
     ^ term synthesized type
         A
       but is being checked against type
         Type
       unequal head terms:
         A
       does not equal
         Type
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def S : Type ≔ sig (x y : a, z : b)
     ^ term synthesized type
         B
       but is being checked against type
         Type
       unequal head terms:
         B
       does not equal
         Type
  
  [1]

The same goes for higher function-types, both instantiated and not.

  $ cat >hp.ny <<EOF
  > axiom A : Type
  > axiom B : A → Type
  > axiom f : (x : A) → B x
  > axiom g : (x : A) → B x
  > def AA : Type ≔ A
  > EOF

  $ narya hp.ny -e 'echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)  echo {A x₁ : A} (x₂ : refl AA A x₁) →⁽ᵉ⁾ refl B x₂ (f A) (g x₁)'
  {x₀ : A} {x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B x₂ (f x₀) (g x₁)
    : Type
  
  {A′ : A} {x₁ : A} (x₂ : Id A A′ x₁) →⁽ᵉ⁾ Id B x₂ (f A′) (g x₁)
    : Type
  

  $ narya hp.ny -e 'echo (x y : Id A) ⇒ Id B x.2  echo (A y : Id AA) ⇒ Id B y.2  echo refl ((x y : Id A) ⇒ Id B x.2)'
  (x : Id A) (y : Id A) ⇒ Id B x.2
    : Type⁽ᵉ⁾ ((x : A) (y : A) → B x) ((x : A) (y : A) → B x)
  
  (A′ : Id A) (y : Id A) ⇒ Id B y.2
    : Type⁽ᵉ⁾ ((A′ : A) (y : A) → B y) ((A′ : A) (y : A) → B y)
  
  (x : A⁽ᵉᵉ⁾) (y : A⁽ᵉᵉ⁾) ⇒ B⁽ᵉᵉ⁾ x.22
    : Type⁽ᵉᵉ⁾ ((x : Id A) (y : Id A) ⇒ Id B x.2)
        ((x : Id A) (y : Id A) ⇒ Id B x.2) ((x : Id A) (y : Id A) ⇒ Id B x.2)
        ((x : Id A) (y : Id A) ⇒ Id B x.2)
  

  $ narya -spatial -e 'def T (U :♭| Type) : Type⁽ᵉ⁾ ((x y :♭| U) → U) ((x y :♭| U) → U) ≔ (x y :♭| Id U) ⇒ Id U  about T'
  U ↦ (x :♭| Id U) (y :♭| Id U) ⇒ Id U
    : (U :♭| Type)
      → Type⁽ᵉ⁾ ((x :♭| U) (y :♭| U) → U) ((x :♭| U) (y :♭| U) → U)
  

With arity zero, a cube has no boundary, so an instantiated higher function-type can bind a group of explicit variables sharing a domain, each forming its own one-domain function-type.

  $ narya -arity 0 -parametric -e 'axiom A : Type  axiom B : A → Type  axiom f : (x : A) (y : A) → B x  echo (A y : Id A .) →⁽ᵉ⁾ Id B y .  def q : (x y : Id A .) →⁽ᵉ⁾ Id B x . ≔ refl f  echo q'
  (A′ : Id A .) (y : Id A .) →⁽ᵉ⁾ Id B y .
    : Type
  
  ap f
    : (x : Id A .) (y : Id A .) →⁽ᵉ⁾ Id B x .
  

Otherwise that isn't allowed, since the later variables would have no boundaries.

  $ narya hp.ny -e 'echo {x₀ x₁ : A} (x₂ y₂ : refl A x₀ x₁) →⁽ᵉ⁾ A'
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ y₂ : refl A x₀ x₁) →⁽ᵉ⁾ A
     ^ invalid higher function-type: a primary domain with boundaries can't be shared by several variables
  
  [1]
