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
  

A neutral that is an applied canonical type is read back and displayed as the corresponding declaration.

  $ narya -e 'def N : Type ≔ data [ zero. | suc. (_ : N) ]' -e 'def List : Type → Type ≔ A ↦ data [ nil. | cons. (x : A) (xs : List A) ]' -e 'def Stream : Type → Type ≔ A ↦ codata [ x .head : A | x .tail : Stream A ]' -e 'def Vec : Type → N → Type ≔ A ↦ data [ nil. : Vec A zero. | cons. : (n : N) → A → Vec A n → Vec A (suc. n) ]' -e 'about (List N)' -e 'about (Stream N)' -e 'about (Vec N (suc. zero.))'
  data [
  | nil.
  | cons. (x : N) (xs : List N) ]
    : Type
  
  codata [
  | 𝑥 .head : N
  | 𝑥 .tail : Stream N ]
    : Type
  
  data [
  | nil.
  | cons. (n : N) (𝑥 : N) (𝑦 : Vec N n) ]
    : Type
  


A higher-dimensional (Gel-like) codatatype is read back at its intrinsic dimension.

  $ narya -dtt -e 'axiom A : Type' -e 'axiom Aʹ : A → Type' -e 'def Gel (A : Type) (Aʹ : A → Type) : Type⁽ᵈ⁾ A ≔ sig x ↦ ( ungel : Aʹ x )' -e 'about (Gel A Aʹ)'
  sig (
    𝑥 .ungel : Aʹ 𝑥.0 )
    : Type⁽ᵈ⁾ A
  


A degenerate codatatype or record is read back at its full dimension, showing the in-practice (higher-dimensional) field types, including higher-pi field types with their boundary faces.

  $ narya -e 'axiom X : Type' -e 'def Stream : Type → Type ≔ A ↦ codata [ x .head : A | x .tail : Stream A ]' -e 'def R : Type ≔ sig ( a : Type, b : (a → Type) )' -e 'about (refl (Stream X))' -e 'about (refl R)'
  codata [
  | 𝑥 .head : Id X (𝑥.0 .head) (𝑥.1 .head)
  | 𝑥 .tail : Stream⁽ᵉ⁾ (Id X) (𝑥.0 .tail) (𝑥.1 .tail) ]
    : Type⁽ᵉ⁾ (Stream X) (Stream X)
  
  sig (
    𝑥 .a : Type⁽ᵉ⁾ (𝑥.0 .a) (𝑥.1 .a),
    𝑥 .b : {𝑥₀ : 𝑥.0 .a} {𝑥₁ : 𝑥.1 .a} (𝑥₂ : 𝑥.2 .a 𝑥₀ 𝑥₁)
           →⁽ᵉ⁾ Type⁽ᵉ⁾ (𝑥.0 .b 𝑥₀) (𝑥.1 .b 𝑥₁) )
    : Type⁽ᵉ⁾ R R
  



