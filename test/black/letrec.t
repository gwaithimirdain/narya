Recursive let-bindings

  $ cat >letrec.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
  > def times (x y : ℕ) : ℕ ≔
  >   let rec plus : ℕ → ℕ → ℕ ≔ m n ↦ match n [ zero. ↦ m | suc. p ↦ suc. (plus m p) ] in
  >   match y [ zero. ↦ zero. | suc. z ↦ plus (times x z) x ]
  > EOF

  $ narya -v letrec.ny -e 'echo times 3 4' -e 'echo times'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant times defined
  
  12
    : ℕ
  
  times
    : (x : ℕ) (y : ℕ) → ℕ
  
In kinetic terms

  $ cat >letrec-k.ny <<EOF
  > def ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ]
  > def idℕ : ℕ → ℕ ≔ x ↦ x
  > def times (x y : ℕ) : ℕ ≔ idℕ
  >   (let rec plus : ℕ → ℕ → ℕ ≔ m n ↦ match n [ zero. ↦ m | suc. p ↦ suc. (plus m p) ] in
  >    match y [ zero. ↦ zero. | suc. z ↦ plus (times x z) x ])
  > EOF

  $ narya -v letrec-k.ny -e 'echo times 3 4' -e 'echo times'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant idℕ defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/letrec-k.ny
   5 |    match y [ zero. ↦ zero. | suc. z ↦ plus (times x z) x ])
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant times defined
  
  12
    : ℕ
  
  times
    : (x : ℕ) (y : ℕ) → ℕ
  
Local recursive datatypes

  $ cat >letrec-ty.ny <<EOF
  > def adder : Type ≔ sig (t : Type, one : t, plus : t → t → t)
  > def ℕadder : adder ≔
  >   let rec ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ] in
  >   let rec plus : ℕ → ℕ → ℕ ≔ x y ↦ match y [ zero. ↦ x | suc. y ↦ suc. (plus x y) ] in
  >   (ℕ, suc. zero., plus)
  > EOF

  $ narya -v letrec-ty.ny -e "echo ℕadder .plus (ℕadder .one) (ℕadder .one)"
   ￫ info[I0000]
   ￮ constant adder defined
  
   ￫ info[I0000]
   ￮ constant ℕadder defined
  
  2
    : _letrec.0.ℕ{…}
  

