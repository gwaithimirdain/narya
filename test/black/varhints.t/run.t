The #(variables ≔ ...) attribute on data, sig, and codata attaches
variable-name hints to a canonical type, which are used when generating
names for unnamed variables belonging to that type.

  $ cat - >hints.ny <<EOF
  > def ℕ : Type ≔ data #(variables ≔ n,m,k) [ zero. | pair. (_ : ℕ) (_ : ℕ) ]
  > def kpair : ℕ → ℕ → ℕ ≔ ((x : ℕ → ℕ → ℕ) ↦ x : ℕ → ℕ → ℕ) pair.
  > echo kpair
  > def prod (A B : Type) : Type ≔ sig #(transparent) #(variables ≔ u,v) (fst : A, snd : B)
  > def Stream (A : Type) : Type ≔ codata #(variables ≔ s) [ x .head : A | x .tail : Stream A ]
  > axiom A : Type
  > axiom f : prod A A → ℕ
  > axiom g : Stream A → ℕ
  > echo Id (prod A A → ℕ) f f
  > echo Id (Stream A → ℕ) g g
  > EOF

  $ narya -parametric hints.ny
  n m ↦ pair. n m
    : ℕ → ℕ → ℕ
  
  {u₀ : prod A A} {u₁ : prod A A} (u₂ : prod⁽ᵉ⁾ (Id A) (Id A) u₀ u₁)
  →⁽ᵉ⁾ ℕ⁽ᵉ⁾ (f (fst ≔ u₀ .fst, snd ≔ u₀ .snd))
         (f (fst ≔ u₁ .fst, snd ≔ u₁ .snd))
    : Type
  
  {s₀ : Stream A} {s₁ : Stream A} (s₂ : Stream⁽ᵉ⁾ (Id A) s₀ s₁)
  →⁽ᵉ⁾ ℕ⁽ᵉ⁾ (g s₀) (g s₁)
    : Type
  

The file is reformatted with the attributes preserved.

  $ cat hints.ny
  def ℕ : Type ≔ data #(variables ≔ n, m, k) [
  | zero.
  | pair. (_ : ℕ) (_ : ℕ) ]
  
  def kpair : ℕ → ℕ → ℕ ≔ ((x : ℕ → ℕ → ℕ) ↦ x : ℕ → ℕ → ℕ) pair.
  
  echo kpair
  
  def prod (A B : Type) : Type ≔ sig #(transparent) #(variables ≔ u, v) (
    fst : A,
    snd : B )
  
  def Stream (A : Type) : Type ≔ codata #(variables ≔ s) [
  | x .head : A
  | x .tail : Stream A ]
  
  axiom A : Type
  
  axiom f : prod A A → ℕ
  
  axiom g : Stream A → ℕ
  
  echo Id (prod A A → ℕ) f f
  
  echo Id (Stream A → ℕ) g g

If there are more unnamed variables than hints, the global default names
are used as a fallback.

  $ narya -e "def P : Type ≔ data #(variables ≔ p) [ mk. (_ : P) (_ : P) ] def kmk : P → P → P ≔ ((x : P → P → P) ↦ x : P → P → P) mk. echo kmk"
  p 𝑥 ↦ mk. p 𝑥
    : P → P → P
  

Type-specific hints take precedence over the global default names set with
the -variables flag.

  $ narya -variables a,b -e "def ℕ : Type ≔ data #(variables ≔ n) [ zero. | suc. (_ : ℕ) ] def ksuc : ℕ → ℕ ≔ ((x : ℕ → ℕ) ↦ x : ℕ → ℕ) suc. echo ksuc def B : Type ≔ data [ true. | false. ] def kif : B → B ≔ ((x : B → B) ↦ x : B → B) (_ ↦ true.)"
  n ↦ suc. n
    : ℕ → ℕ
  

The names given in a variables attribute must be valid variable names, and
unrecognized attributes are errors.

  $ narya -e "def X : Type ≔ data #(variables ≔ 42) [ zero. ]"
   ￫ error[E0202]
   ￭ command-line exec string
   1 | def X : Type ≔ data #(variables ≔ 42) [ zero. ]
     ^ invalid local variable name: 42
  
  [1]

  $ narya -e "def X : Type ≔ sig #(variables ≔ a.b) (x : Type)"
   ￫ error[E0202]
   ￭ command-line exec string
   1 | def X : Type ≔ sig #(variables ≔ a.b) (x : Type)
     ^ invalid local variable name: a.b
  
  [1]

  $ narya -e "def X : Type ≔ sig #(variables ≔ _) (x : Type)"
   ￫ error[E0202]
   ￭ command-line exec string
   1 | def X : Type ≔ sig #(variables ≔ _) (x : Type)
     ^ invalid local variable name: _
  
  [1]

  $ narya -e "def X : Type ≔ data #(variables) [ zero. ]"
   ￫ error[E0208]
   ￭ command-line exec string
   1 | def X : Type ≔ data #(variables) [ zero. ]
     ^ unrecognized attribute
  
  [1]

  $ narya -e "def X : Type ≔ data #(transparent) [ zero. ]"
   ￫ error[E0208]
   ￭ command-line exec string
   1 | def X : Type ≔ data #(transparent) [ zero. ]
     ^ unrecognized attribute
  
  [1]

  $ narya -e "def X : Type ≔ codata #(opaque) [ ]"
   ￫ error[E0208]
   ￭ command-line exec string
   1 | def X : Type ≔ codata #(opaque) [ ]
     ^ unrecognized attribute
  
  [1]

The contexts of holes also use the hints for anonymous variables.

  $ cat - >holes.ny <<EOF
  > def ℕ : Type ≔ data #(variables ≔ n,m,k) [ zero. | suc. (_ : ℕ) ]
  > def foo : ℕ → ℕ → ℕ ≔ _ _ ↦ ?
  > def bar (n : ℕ) : ℕ → ℕ ≔ _ ↦ ?
  > EOF

  $ narya -v holes.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant foo defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     m : ℕ (not in scope)
     n : ℕ (not in scope)
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0000]
   ￮ constant bar defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     n : ℕ
     m : ℕ (not in scope)
     ----------------------------------------------------------------------
     ℕ
  
   ￫ error[E3002]
   ￮ file holes.ny contains open holes
  
  [1]


The "split" interactive command also uses the hints when generating names
for the variables of the abstractions and matches that it proposes.

  $ narya -fake-interact "def ℕ : Type ≔ data #(variables ≔ n,m,k) [ zero. | suc. (_ : ℕ) | pair. (_ : ℕ) (_ : ℕ) ] def foo : ℕ → ℕ → ℕ ≔ ? split 0 ≔ _ def bar (x : ℕ) : ℕ ≔ ? split 1 ≔ x"
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant foo defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     ℕ → ℕ → ℕ
  
   ￫ info[I0009]
   ￮ split successful, hole could be solved by:
       n m ↦ ?
  
   ￫ info[I0000]
   ￮ constant bar defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     x : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0009]
   ￮ split successful, hole could be solved by:
       match x [ zero. ↦ ? | suc. n ↦ ? | pair. n m ↦ ? ]
  
