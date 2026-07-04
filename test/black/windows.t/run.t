Composition of modal operators is preserved up to isomorphism:

  $ narya -v -composed-functors compose.ny
   ￫ info[I0000]
   ￮ constant F defined
  
   ￫ info[I0000]
   ￮ constant G defined
  
   ￫ info[I0000]
   ￮ constant GF defined
  
   ￫ info[I0000]
   ￮ constant fwd defined
  
   ￫ info[I0000]
   ￮ constant bwd defined
  
   ￫ info[I0000]
   ￮ constant fwd∘bwd defined
  
   ￫ info[I0000]
   ￮ constant bwd∘fwd defined
  

Matching with the wrong window modality is an error:

  $ narya -composed-functors compose.ny -e "def fwd2 (X :G F| AType) (u : G (F X)) : GF X ≔ match u [ g. y ↦ match (y :G F| _) [ f. x ↦ gf. x ]]"
   ￫ error[E1701]
   ￭ command-line exec string
   1 | def fwd2 (X :G F| AType) (u : G (F X)) : GF X ≔ match u [ g. y ↦ match (y :G F| _) [ f. x ↦ gf. x ]]
     ^ modality mismatch in checking implicit match (G F ≠ G)
  
  [1]

A transparent modal operator preserves the empty type and binary disjoint
unions up to isomorphism:

  $ narya -v -functor preserve.ny
   ￫ info[I0000]
   ￮ constant ○ defined
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant ⊥' defined
  
   ￫ info[I0000]
   ￮ constant zfwd defined
  
   ￫ info[I0000]
   ￮ constant zbwd defined
  
   ￫ info[I0000]
   ￮ constant zbwd∘zfwd defined
  
   ￫ info[I0000]
   ￮ constant zfwd∘zbwd defined
  
   ￫ info[I0000]
   ￮ constant sum defined
  
   ￫ info[I0000]
   ￮ constant sum' defined
  
   ￫ info[I0000]
   ￮ constant sfwd defined
  
   ￫ info[I0000]
   ￮ constant sbwd defined
  
   ￫ info[I0000]
   ￮ constant sbwd∘sfwd defined
  
   ￫ info[I0000]
   ￮ constant sfwd∘sbwd defined
  

Refuting a modal variable requires a window modality:

  $ narya -functor preserve.ny -e "def zfwd2 (u : ○ ⊥) : ⊥' ≔ match u [ circle. x ↦ match x [ ] ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def zfwd2 (u : ○ ⊥) : ⊥' ≔ match u [ circle. x ↦ match x [ ] ]
     ^ use of ○ variable behind id lock requires a key
  
  [1]
