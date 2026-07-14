  $ narya -v -gwpt gwpt.ny
   ￫ info[I0000]
   ￮ constant counit defined
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant eta defined
  
   ￫ info[I0000]
   ￮ constant counit2 defined
  
   ￫ info[I0000]
   ￮ constant epsilon defined
  
   ￫ info[I0000]
   ￮ constant E defined
  
   ￫ info[I0000]
   ￮ constant epsilon_inv defined
  
   ￫ info[I0000]
   ￮ constant theta defined
  
   ￫ info[I0000]
   ￮ constant phi defined
  
   ￫ info[I0000]
   ￮ constant isos defined
  
   ￫ info[I0000]
   ￮ constant C defined
  
   ￫ info[I0000]
   ￮ constant eta' defined
  
   ￫ info[I0000]
   ￮ constant C2 defined
  
   ￫ info[I0000]
   ￮ constant eta'2 defined
  
   ￫ info[I0000]
   ￮ constant boxdia defined
  
   ￫ info[I0000]
   ￮ constant trinab defined
  
   ￫ info[I0000]
   ￮ constant trinab2 defined
  
   ￫ info[I0000]
   ￮ constant □ defined
  
   ￫ info[I0000]
   ￮ constant box defined
  
   ￫ info[I0000]
   ￮ constant unbox defined
  
   ￫ info[I0000]
   ￮ constant unbox_box defined
  
   ￫ info[I0000]
   ￮ constant ∇′ defined
  
   ￫ info[I0000]
   ￮ constant nab defined
  
   ￫ info[I0000]
   ￮ constant unnab defined
  
   ￫ info[I0000]
   ￮ constant unnab_nab defined
  
   ￫ info[I0000]
   ￮ constant ∇″ defined
  
   ￫ info[I0000]
   ￮ constant nab_unnab defined
  
   ￫ info[I0000]
   ￮ constant nab_eta defined
  
   ￫ info[I0000]
   ￮ constant NB defined
  
   ￫ info[I0000]
   ￮ constant mk defined
  
   ￫ info[I0000]
   ￮ constant unmk defined
  
   ￫ info[I0000]
   ￮ constant unmk_mk defined
  

The unit of ◇ ⊣ ∇ is not invertible: there is no 2-cell ∇◇ ⇒ 1.

  $ narya -gwpt gwpt.ny -e "def bad (A : Type) (x : ∇◇ | A) : A ≔ x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad (A : Type) (x : ∇◇ | A) : A ≔ x
     ^ use of ∇◇ variable behind id lock requires a key
  
  [1]

Nor are there 2-cells □△ ⇒ 1 or 1 ⇒ △□ (the adjunction △ ⊣ □ is free).

  $ narya -gwpt gwpt.ny -e "def bad2 (A : □△ | Disc) (x : □△ | A) : A ≔ x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad2 (A : □△ | Disc) (x : □△ | A) : A ≔ x
     ^ use of □△ variable behind id lock requires a key
  
  [1]

  $ narya -gwpt gwpt.ny -e "def bad3 (A : Type) : Type ≔ data [ bad3. (_ : △□ | A) ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad3 (A : Type) : Type ≔ data [ bad3. (_ : △□ | A) ]
     ^ use of id variable behind △□ lock requires a key
  
  [1]

The induced 2-cells go from □ to ◇ and from △ to ∇, not the other way.

  $ narya -gwpt gwpt.ny -e "def bad4 (X : ◇ | Type) : Disc ≔ data [ bad4. (_ : □ | X) ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad4 (X : ◇ | Type) : Disc ≔ data [ bad4. (_ : □ | X) ]
     ^ use of ◇ variable behind □ lock requires a key
  
  [1]

  $ narya -gwpt gwpt.ny -e "def bad5 (X : ∇ | Disc) : Type ≔ data [ bad5. (_ : △ | X) ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def bad5 (X : ∇ | Disc) : Type ≔ data [ bad5. (_ : △ | X) ]
     ^ use of ∇ variable behind △ lock requires a key
  
  [1]

There are two distinct 2-cells △□ ⇒ ∇◇: the counit ε followed by the unit η',
or the two induced strands □ ⇒ ◇ and △ ⇒ ∇ side by side.  So an implicit key
cannot be inserted.

  $ narya -gwpt gwpt.ny -e "def amb (A : △□ | Type) (x : △□ | A) : C A ≔ c. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def amb (A : △□ | Type) (x : △□ | A) : C A ≔ c. x
     ^ use of △□ variable behind ∇◇ lock requires a key
  
  [1]

Likewise there are two distinct 2-cells △□ ⇒ ∇□△◇.

  $ narya -gwpt gwpt.ny -e "def amb2 (A : △□ | Type) (x : △□ | A) : C2 A ≔ c2. x"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def amb2 (A : △□ | Type) (x : △□ | A) : C2 A ≔ c2. x
     ^ use of △□ variable behind ∇□△◇ lock requires a key
  
  [1]

And the walking-adjunction ambiguity of the two whiskered units □△ ⇒ □△□△ is
still present.

  $ narya -gwpt gwpt.ny -e "def amb3 (A : Disc) (x : □△ | A) : T (T A) ≔ t. (t. x)"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def amb3 (A : Disc) (x : □△ | A) : T (T A) ≔ t. (t. x)
     ^ use of □△ variable behind □△□△ lock requires a key
  
  [1]
