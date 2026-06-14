About: display the potential value (canonical type or case tree) of a neutral

  $ narya -e 'def N : Type ≔ data [ zero. | suc. (_ : N) ]' -e 'def Stream : Type → Type ≔ A ↦ codata [ x .head : A | x .tail : Stream A ]' -e 'def R : Type ≔ sig ( a : Type, b : (a → Type) )' -e 'def pred : N → N ≔ [ zero. ↦ zero. | suc. n ↦ n ]' -e 'axiom ax : N' -e 'echo N' -e 'about N' -e 'about Stream' -e 'about R' -e 'about pred' -e 'about ax' -e 'about (pred (suc. zero.))'
  N
    : Type
  
  data [
  | zero.
  | suc. (𝑥 : N) ]
    : Type
  
  A ↦ codata [ 𝑥 .head : A | 𝑥 .tail : Stream A ]
    : Type → Type
  
  sig (
    𝑥 .a : Type,
    𝑥 .b : 𝑥 .a → Type )
    : Type
  
  𝑥 ↦ match 𝑥 [ suc. 𝑦 ↦ 𝑦 | zero. ↦ 0 ]
    : N → N
  
  ax
    : N
  
  0
    : N
  
