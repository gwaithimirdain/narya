About: display the definition of a constant.  A bare constant is displayed as its stored definition: a canonical type as its declaration, a function defined by matching with its matches, and so on.  Anything else is displayed as its normal form, like "echo".

  $ narya -e 'def N : Type ≔ data [ zero. | suc. (_ : N) ]' -e 'def Stream : Type → Type ≔ A ↦ codata [ x .head : A | x .tail : Stream A ]' -e 'def R : Type ≔ sig ( a : Type, b : (a → Type) )' -e 'def pred : N → N ≔ [ zero. ↦ zero. | suc. n ↦ n ]' -e 'axiom ax : N' -e 'echo N' -e 'about N' -e 'about Stream' -e 'about R' -e 'about pred' -e 'about ax' -e 'about (pred (suc. zero.))'
  N
    : Type
  
  data [
  | zero. : N
  | suc. (𝑥 : N) : N ]
    : Type
  
  A ↦ codata [ x .head : A | x .tail : Stream A ]
    : Type → Type
  
  sig (
    a : Type,
    b : a → Type )
    : Type
  
  𝑥 ↦ match 𝑥 [ suc. n ↦ n | zero. ↦ 0 ]
    : N → N
  
  ax
    : N
  
  0
    : N
  

"about" on a datatype constant itself (a parameter abstraction reaching a datatype) shows the parameters abstracted and the constructors' output types referring to the parameterized family.

  $ narya -e 'def N : Type ≔ data [ zero. | suc. (_ : N) ]' -e 'def Vec : Type → N → Type ≔ A ↦ data [ nil. : Vec A zero. | cons. : (n : N) → A → Vec A n → Vec A (suc. n) ]' -e 'about Vec'
  A ↦
  data [
  | nil. : Vec A 0
  | cons. (n : N) (𝑥 : A) (𝑦 : Vec A n) : Vec A (suc. n) ]
    : Type → N → Type
  


A datatype defined nested inside a case tree is reached through the tree rather than as a top-level canonical type, so "about" displays the stored case tree.  Each nested datatype's constructor output types are shown faithfully (with the real datatype head) from the stored output term.

  $ narya -e 'def N : Type ≔ data [ zero. | suc. (_ : N) ]' -e 'def W (n : N) : N → Type ≔ match n [ zero. ↦ data [ w0. : W n zero. ] | suc. m ↦ data [ w1. : W n (suc. m) ] ]' -e 'about W'
  n ↦
  match n [
  | suc. m ↦ data [
    | w1. : W n (suc. m) ]
  | zero. ↦ data [
    | w0. : W n 0 ]]
    : (n : N) → N → Type
  
