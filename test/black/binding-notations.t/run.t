Binding notations

  $ narya -v sigma.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/prelude.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom C assumed
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0002]
   ￮ notation «_ × _» defined
  
   ￫ info[I0001]
   ￮ axiom ex assumed
  
   ￫ info[I0002]
   ￮ notation «∃ _ , _» defined
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/prelude.ny (source)
  
  (x : A) × B x
    : Type
  
  A × C
    : Type
  
  (x : A) × (y : A) × Id A x y
    : Type
  
  (x : A) × B x
    : Type
  
   ￫ info[I0000]
   ￮ constant pr defined
  
  pr
    : (p : (x : A) × B x) → A
  
  Σ A B
    : Type
  
  A × C
    : Type
  
   ￫ info[I0000]
   ￮ constant AA defined
  
  A × C
    : Type
  
   ￫ info[I0001]
   ￮ axiom x assumed
  
  (x′ : A) × Id A x x′
    : Type
  
  ∃ x , B x
    : Type
  
  ∃ x , B x
    : Type
  
  ∃ 𝑥 , C
    : Type
  
  ex B
    : Type
  
   ￫ info[I0001]
   ￮ axiom int assumed
  
   ￫ info[I0002]
   ￮ notation «∫ _ d _» defined
  
  ∫ x d x
    : A
  
   ￫ info[I0001]
   ￮ axiom curry assumed
  
   ￫ info[I0002]
   ￮ notation «λ² _ , _ . _» defined
  
  λ² x , y . x
    : A
  
   ￫ info[I0000]
   ￮ constant Tree defined
  
   ￫ info[I0002]
   ￮ notation «node _ , _» defined
  
   ￫ info[I0000]
   ￮ constant t defined
  
  node x , node y , leaf.
    : Tree
  

The notations survive compilation

  $ cat >use.ny <<'EOS'
  > import "prelude"
  > echo (x : A) × B x
  > def h : Type ≔ (x : A) × ?
  > EOS
  $ narya -v use.ny 2>&1 | grep -v "^ *$"
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/prelude.ny (compiled)
  (x : A) × B x
    : Type
   ￫ info[I0000]
   ￮ constant h defined, containing 1 hole
   ￫ info[I3003]
   ￮ hole ?0:
     x : A
     ----------------------------------------------------------------------
     Type
   ￫ error[E3002]
   ￮ file use.ny contains open holes

Errors when using binding notations

  $ narya prelude.ny -e "echo ∃ (a b), B a"
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo ∃ (a b), B a
     ^ parse error: invalid variable
  
  [1]

  $ narya prelude.ny -e "echo ∃ (x y : A), B x"
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo ∃ (x y : A), B x
     ^ parse error: this notation binds only one variable here
  
  [1]

  $ narya prelude.ny -e "echo (x y : A) × B x"
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo (x y : A) × B x
     ^ parse error: this notation binds only one variable here
  
  [1]

  $ narya prelude.ny -e "echo ∃ {x : A}, B x"
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo ∃ {x : A}, B x
     ^ parse error: this notation can't bind an implicit variable
  
  [1]

  $ narya prelude.ny -e "def Tree : Type ≔ data [ leaf. | node. (f : A → Tree) ]" -e "notation(0) \"node\" x \",\" t … ≔ node. (x ↦ t)" -e "def f (t : Tree) : Tree ≔ match t [ leaf. ↦ leaf. | node x, s ↦ leaf. ]"
   ￫ error[E0200]
   ￭ command-line exec string
   1 | def f (t : Tree) : Tree ≔ match t [ leaf. ↦ leaf. | node x, s ↦ leaf. ]
     ^ parse error: a notation that binds variables can't be used in a pattern
  
  [1]

Errors when defining binding notations

  $ narya prelude.ny -e "notation(0) \"∀\" x \",\" P ≔ ex (x x ↦ P)"
   ￫ error[E2207]
   ￮ notation variable 'x' used twice
  
  [1]

  $ narya prelude.ny -e "notation(0) \"∀\" x \",\" P ≔ ex (x ↦ x)"
   ￫ error[E2207]
   ￮ notation variable 'x' used twice
  
  [1]

  $ narya prelude.ny -e "notation(0) \"∀\" (x : X) \",\" P ≔ ex (P ↦ x)"
   ￫ error[E2206]
   ￮ unused notation variable: 'X'
  
  [1]

  $ narya prelude.ny -e "notation(0) \"∀\" (x : X) \",\" P ≔ Σ x (X ↦ P)"
   ￫ error[E2211]
   ￮ invalid binding in notation: variable 'x' of a typed binder must be bound by an abstraction
  
  [1]

  $ narya prelude.ny -e "notation(0) \"∀\" (x : X) \",\" P ≔ Σ X P"
   ￫ error[E2206]
   ￮ unused notation variable: 'x'
  
  [1]

  $ narya prelude.ny -e "notation(0) \"∀\" x \",\" y \",\" P ≔ ex (x y ↦ P)"
   ￫ error[E2211]
   ￮ invalid binding in notation: argument (x y ↦ P) of ex must have a function-type with at least 2 arguments, but its type has only 1
  
  [1]

  $ narya prelude.ny -e "notation(0) \"∀\" x \",\" P ≔ Σ (x ↦ P)"
   ￫ error[E2211]
   ￮ invalid binding in notation: argument (x ↦ P) of Σ must have a function-type with at least 1 argument, but its type is not a function-type
  
  [1]

  $ narya prelude.ny -e "axiom K : Type" -e "notation(0) \"∀\" Q \",\" x \",\" P ≔ K Q (x ↦ P)"
   ￫ error[E2211]
   ￮ invalid binding in notation: K doesn't take enough arguments for this notation
  
  [1]

  $ narya prelude.ny -e "axiom F : Type → Type" -e "notation(0) \"∀\" x \",\" P ≔ F (x ↦ P)"
   ￫ error[E2211]
   ￮ invalid binding in notation: argument (x ↦ P) of F must have a function-type with at least 1 argument, but its type is not a function-type
  
  [1]

  $ narya prelude.ny -e "axiom G : (A → A → Type) → Type" -e "notation(0) \"∀\" x \",\" P ≔ G (x ↦ P)" -e "echo ∀ x, (y ↦ Id A x y)" -e "axiom R : A → A → Type" -e "echo G R"
  ∀ x , (y ↦ Id A x y)
    : Type
  
  G R
    : Type
  

  $ narya prelude.ny -e "axiom H : (Fam : Type) → Fam → Type" -e "notation(0) \"∀\" F \",\" x \",\" P ≔ H F (x ↦ P)"
   ￫ error[E2211]
   ￮ invalid binding in notation: argument (x ↦ P) of H must have a function-type with at least 1 argument, but its type is not a function-type
  
  [1]

  $ narya prelude.ny -e "def AF : Type ≔ A → Type" -e "axiom J : AF → Type" -e "notation(0) \"∀\" x \",\" P ≔ J (x ↦ P)" -e "echo ∀ x, B x"
  ∀ x , B x
    : Type
  

Reformatting a notation command

  $ cat >reformat.ny <<'EOS'
  > import "prelude"
  > notation(1) ( x:X ) "×" Y …  ≔  Σ X (  x ↦ {` a comment `} Y )
  > axiom curry : (A → A → A) → A
  > notation(0) "λ²" x "," y "." b ≔ curry ( x y↦b )
  > EOS
  $ narya reformat.ny
   ￫ warning[E2209]
   ￮ replacing printing notation for Σ (previous notation will still be parseable)
  
  $ cat reformat.ny
  import "prelude"
  
  notation(1) (x : X) "×" Y … ≔ Σ X (x ↦ {` a comment `} Y)
  
  axiom curry : (A → A → A) → A
  
  notation(0) "λ²" x "," y "." b ≔ curry (x y ↦ b)
