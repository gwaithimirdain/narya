  $ narya -v -adjunction adjunction.ny
   ￫ info[I0000]
   ￮ constant counit defined
  
   ￫ info[I0000]
   ￮ constant counit2 defined
  
   ￫ info[I0000]
   ￮ constant □△ defined
  
   ￫ info[I0000]
   ￮ constant □△□△ defined
  
   ￫ info[I0000]
   ￮ constant eta defined
  
   ￫ info[I0000]
   ￮ constant eta2 defined
  
   ￫ info[I0000]
   ￮ constant mu defined
  
   ￫ info[I0000]
   ￮ constant △□ defined
  
   ￫ info[I0000]
   ￮ constant □ defined
  
   ￫ info[I0000]
   ￮ constant box defined
  
   ￫ info[I0000]
   ￮ constant unbox defined
  
   ￫ info[I0000]
   ￮ constant unbox_box defined
  
   ￫ info[I0000]
   ￮ constant □′ defined
  
   ￫ info[I0000]
   ￮ constant box_unbox defined
  
   ￫ info[I0000]
   ￮ constant box_eta defined
  

The reflector □△ is not invertible: there is no 2-cell □△ ⇒ 1.

  $ narya -adjunction adjunction.ny -e "def bad (A :□△| Disc) (x :□△| A) : A ≔ x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad (A :□△| Disc) (x :□△| A) : A ≔ x
     ^ use of □△ variable behind id lock requires a key
  
  [1]

Nor is there a 2-cell 1 ⇒ △□.

  $ narya -adjunction adjunction.ny -e "def bad2 (A : Type) : Type ≔ data [ bad2. (_ :△□| A) ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad2 (A : Type) : Type ≔ data [ bad2. (_ :△□| A) ]
     ^ use of id variable behind △□ lock requires a key
  
  [1]

There are two distinct 2-cells □△ ⇒ □△□△ (whiskering the unit on either
side), so an implicit key cannot be inserted.

  $ narya -adjunction adjunction.ny -e "def amb (A : Disc) (x :□△| A) : □△□△ A ≔ t2. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def amb (A : Disc) (x :□△| A) : □△□△ A ≔ t2. x
     ^ use of □△ variable behind □△□△ lock requires a key
  
  [1]

Likewise there are two distinct 2-cells △□△□ ⇒ △□ (whiskering the counit on
either side).

  $ narya -adjunction adjunction.ny -e "def amb2 (A :△□| Type) (x :△□△□| A) : △□ A ≔ s. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def amb2 (A :△□| Type) (x :△□△□| A) : △□ A ≔ s. x
     ^ use of △□△□ variable behind △□ lock requires a key
  
  [1]

But △□△□ ⇒ 1 is unique, since the two whiskered counits have the same pairing
after composing with the outer counit.

  $ narya -adjunction adjunction.ny -e "def counit22 (A :△□△□| Type) (x :△□△□| A) : A ≔ x"

The modality □ (or △) alone admits no 2-cell to the identity.

  $ narya -adjunction adjunction.ny -e "def bad3 (A :□| Type) (x :□| A) : A ≔ x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad3 (A :□| Type) (x :□| A) : A ≔ x
     ^ use of □ variable behind id lock requires a key
  
  [1]
