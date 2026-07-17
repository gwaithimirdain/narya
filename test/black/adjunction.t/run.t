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
  
   ￫ info[I0000]
   ￮ constant needs_key1 defined
  
   ￫ info[I0000]
   ￮ constant needs_key2 defined
  
   ￫ info[I0000]
   ￮ constant needs_key3 defined
  
   ￫ info[I0000]
   ￮ constant needs_key_23 defined
  
   ￫ info[I0000]
   ￮ constant needs_key1a defined
  

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

Different keys are different.

  $ narya -adjunction adjunction.ny -e "def needs_key_12 (A : Disc) (x :□△| A) : Id (□△□△ A) (needs_key1 A x) (needs_key2 A x) ≔ refl _"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | def needs_key_12 (A : Disc) (x :□△| A) : Id (□△□△ A) (needs_key1 A x) (needs_key2 A x) ≔ refl _
     ^ term synthesized type
         □△□△⁽ᵉ⁾ (Id A)
           (t2.
              (x #□△ #□△ #□△ #□.△ #□△ #□△ #□.△ #□△ #□△.η #□.△.□.△ #□△□△ #□△□△ #□△□△
                 #□.△.□.△ #□.△.□.△ #□△□△ #□△□△ #□.△.□.△ #□△□△))
           (t2.
              (x #□△ #□△ #□△ #□.△ #□△ #□△ #□.△ #□△ #□△.η #□.△.□.△ #□△□△ #□△□△ #□△□△
                 #□.△.□.△ #□.△.□.△ #□△□△ #□△□△ #□.△.□.△ #□△□△))
       but is being checked against type
         □△□△⁽ᵉ⁾ (Id A)
           (t2.
              (x #□△ #□△ #□.△ #□△ #□△ #□.△ #□△ #η.□△ #□.△.□.△ #□△□△ #□△□△ #□△□△
                 #□.△.□.△))
           (t2.
              (x #□△ #□△ #□.△ #□△ #□△ #□.△ #□△ #□△.η #□.△.□.△ #□△□△ #□△□△ #□△□△
                 #□.△.□.△))
       unequal head terms:
         x #□△ #□△ #□△ #□.△ #□△ #□△ #□.△ #□△ #□△.η #□.△.□.△ #□△□△ #□△□△ #□△□△ #□.△.□.△
           #□.△.□.△ #□△□△ #□△□△ #□.△.□.△ #□△□△
       does not equal
         x #□△ #□△ #□.△ #□△ #□△ #□.△ #□△ #η.□△ #□.△.□.△ #□△□△ #□△□△ #□△□△ #□.△.□.△
  
  [1]

  $ narya -v -discrete-adjunction -parametric -external -direction p,rel,Br discrete_adjunction.ny
   ￫ info[I0000]
   ￮ constant △ defined
  
   ￫ info[I0000]
   ￮ constant □ defined
  
   ￫ info[I0000]
   ￮ constant eq defined
  
   ￫ info[I0000]
   ￮ constant Br_△ defined
  
   ￫ info[I0000]
   ￮ constant Br_to_eq defined
  
   ￫ info[I0000]
   ￮ constant eq_to_Br defined
  
   ￫ info[I0000]
   ￮ constant eq_to_Br_to_eq defined
  
   ￫ info[I0000]
   ￮ constant Br_to_eq_to_Br defined
  
