Composition of modal operators is preserved up to isomorphism:

  $ narya -v -composable-functors compose.ny
   ￫ info[I0000]
   ￮ constant ○ defined
  
   ￫ info[I0000]
   ￮ constant ▱ defined
  
   ￫ info[I0000]
   ￮ constant ▱○ defined
  
   ￫ info[I0000]
   ￮ constant colax defined
  
   ￫ info[I0000]
   ￮ constant lax defined
  
   ￫ info[I0000]
   ￮ constant lax′ defined
  
   ￫ info[I0000]
   ￮ constant lax″ defined
  
   ￫ info[I0000]
   ￮ constant lax∘colax defined
  
   ￫ info[I0000]
   ￮ constant colax∘lax defined
  

Matching with the wrong window modality is an error:

  $ narya -composable-functors compose.ny -e "def fwd2 (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [ par. y ↦ match (y :▱○| _) [ circ. x ↦ parcirc. x ]]"
   ￫ error[E1701]
   ￭ command-line exec string
   1 | def fwd2 (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [ par. y ↦ match (y :▱○| _) [ circ. x ↦ parcirc. x ]]
     ^ modality mismatch in checking implicit match (▱○ ≠ ▱)
  
  [1]

A transparent modal operator preserves the empty type and binary disjoint
unions up to isomorphism:

  $ narya -v -transparent-functor preserve.ny
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
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant R defined
  
   ￫ info[I0000]
   ￮ constants defined mutually:
       X
       Y
  
   ￫ info[I0000]
   ￮ constant ytest defined
  
   ￫ info[I0000]
   ￮ constant V defined
  
   ￫ hint[E1101]
   ￭ $TESTCASE_ROOT/preserve.ny
   80 | | circle. w ↦ match (w :○| _) [ vnil. ↦ circle. (vnil.) ]]
      ^ match will not refine the goal or context (index is not a free variable):
          0
  
   ￫ info[I0000]
   ￮ constant vtest defined
  

Refuting a modal variable requires a window modality:

  $ narya -transparent-functor preserve.ny -e "def zfwd2 (u : ○ ⊥) : ⊥' ≔ match u [ circle. x ↦ match x [ ] ]"
   ￫ error[E1705]
   ￭ command-line exec string
   1 | def zfwd2 (u : ○ ⊥) : ⊥' ≔ match u [ circle. x ↦ match x [ ] ]
     ^ use of ○ variable behind id lock requires a key
  
  [1]

Since ○ is transparent but not pellucid, it cannot be used as a window for
recursive datatypes, even ones with a single constructor, or datatypes that
mention their mutual companions:

  $ narya -transparent-functor preserve.ny -e "def nbad (u : ○ ℕ) : ○ ℕ ≔ match u [ circle. w ↦ match (w :○| _) [ zero. ↦ u | suc. n ↦ u ] ]"
   ￫ error[E1707]
   ￭ command-line exec string
   1 | def nbad (u : ○ ℕ) : ○ ℕ ≔ match u [ circle. w ↦ match (w :○| _) [ zero. ↦ u | suc. n ↦ u ] ]
     ^ window modality ○ must be pellucid since the datatype has recursive constructors
  
  [1]

  $ narya -transparent-functor preserve.ny -e "def rbad (u : ○ R) : ⊥' ≔ match u [ circle. w ↦ match (w :○| _) [ r. y ↦ rbad (circle. y) ] ]"
   ￫ error[E1707]
   ￭ command-line exec string
   1 | def rbad (u : ○ R) : ⊥' ≔ match u [ circle. w ↦ match (w :○| _) [ r. y ↦ rbad (circle. y) ] ]
     ^ window modality ○ must be pellucid since the datatype has recursive constructors
  
  [1]

  $ narya -transparent-functor preserve.ny -e "def xbad (u : ○ X) : ○ Y ≔ match u [ circle. w ↦ match (w :○| _) [ x. v ↦ circle. v ] ]"
   ￫ error[E1707]
   ￭ command-line exec string
   1 | def xbad (u : ○ X) : ○ Y ≔ match u [ circle. w ↦ match (w :○| _) [ x. v ↦ circle. v ] ]
     ^ window modality ○ must be pellucid since the datatype has recursive constructors
  
  [1]

Recursion is detected in datatypes defined by let rec, but a non-recursive
let rec datatype is still non-recursive:

  $ narya -transparent-functor preserve.ny -e "def LT : DomType ≔ let rec T : DomType ≔ data [ t. (_ : T) ] in T" -e "def lbad (u : ○ LT) : ○ LT ≔ match u [ circle. w ↦ match (w :○| _) [ t. y ↦ circle. y ] ]"
   ￫ error[E1707]
   ￭ command-line exec string
   1 | def lbad (u : ○ LT) : ○ LT ≔ match u [ circle. w ↦ match (w :○| _) [ t. y ↦ circle. y ] ]
     ^ window modality ○ must be pellucid since the datatype has recursive constructors
  
  [1]

  $ narya -v -transparent-functor preserve.ny -e "def LN : DomType ≔ let rec T : DomType ≔ data [ n. ] in T" -e "def lgood (u : ○ LN) : ○ LN ≔ match u [ circle. w ↦ match (w :○| _) [ n. ↦ circle. (n.) ] ]" 2>&1 | tail -4
  
   ￫ info[I0000]
   ￮ constant lgood defined
  

Recursion hiding in the value of a let-bound variable is also detected, while
a clean let-bound variable is fine:

  $ narya -transparent-functor preserve.ny -e "def DD : DomType ≔ let Z ≔ ((DD → DD) : DomType) in data [ d. (_ : Z) ]" -e "def dbad (u : ○ DD) : ○ DD ≔ match u [ circle. w ↦ match (w :○| _) [ d. y ↦ u ] ]"
   ￫ error[E1707]
   ￭ command-line exec string
   1 | def dbad (u : ○ DD) : ○ DD ≔ match u [ circle. w ↦ match (w :○| _) [ d. y ↦ u ] ]
     ^ window modality ○ must be pellucid since the datatype has recursive constructors
  
  [1]

  $ narya -v -transparent-functor preserve.ny -e "def DN : DomType ≔ let Z ≔ (ℕ : DomType) in data [ d. (_ : Z) ]" -e "def dgood (u : ○ DN) : ○ DN ≔ match u [ circle. w ↦ match (w :○| _) [ d. y ↦ u ] ]" 2>&1 | tail -4
  
   ￫ info[I0000]
   ￮ constant dgood defined
  

A datatype with an unsolved hole in a constructor type might turn out to be
recursive, so it conservatively rejects non-pellucid windows; solving the hole
with something non-recursive lifts the restriction, while solving it
recursively makes it permanent:

  $ narya -transparent-functor preserve.ny -fake-interact "def H : DomType ≔ data [ h. (_ : ?) ] def hbad (u : ○ H) : ○ H ≔ match u [ circle. w ↦ match (w :○| _) [ h. y ↦ circle. (h. y) ] ]"
   ￫ info[I0000]
   ￮ constant H defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     DomType
  
   ￫ error[E1707]
   ￭ command line fake-interact
   1 | def H : DomType ≔ data [ h. (_ : ?) ] def hbad (u : ○ H) : ○ H ≔ match u [ circle. w ↦ match (w :○| _) [ h. y ↦ circle. (h. y) ] ]
     ^ window modality ○ must be pellucid since it is not yet known whether the datatype has recursive constructors, due to unsolved holes in its constructor types
  

  $ narya -transparent-functor preserve.ny -fake-interact "def H : DomType ≔ data [ h. (_ : ?) ] solve 0 ≔ ⊥ def hgood (u : ○ H) : ○ H ≔ match u [ circle. w ↦ match (w :○| _) [ h. y ↦ circle. (h. y) ] ]"
   ￫ info[I0000]
   ￮ constant H defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     DomType
  
   ￫ info[I0005]
   ￮ hole solved
  
   ￫ info[I0000]
   ￮ constant hgood defined
  

  $ narya -transparent-functor preserve.ny -fake-interact "def H : DomType ≔ data [ h. (_ : ?) ] solve 0 ≔ H def hbad (u : ○ H) : ○ H ≔ match u [ circle. w ↦ match (w :○| _) [ h. y ↦ circle. (h. y) ] ]"
   ￫ info[I0000]
   ￮ constant H defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     DomType
  
   ￫ info[I0005]
   ￮ hole solved
  
   ￫ error[E1707]
   ￭ command line fake-interact
   1 | def H : DomType ≔ data [ h. (_ : ?) ] solve 0 ≔ H def hbad (u : ○ H) : ○ H ≔ match u [ circle. w ↦ match (w :○| _) [ h. y ↦ circle. (h. y) ] ]
     ^ window modality ○ must be pellucid since the datatype has recursive constructors
  

A datatype defined inside a hole solution that mentions its enclosing constant
is recursive:

  $ narya -transparent-functor preserve.ny -fake-interact "def K : DomType ≔ ? solve 0 ≔ data [ k. (_ : K) ] def kbad (u : ○ K) : ○ K ≔ match u [ circle. w ↦ match (w :○| _) [ k. y ↦ circle. (k. y) ] ]"
   ￫ info[I0000]
   ￮ constant K defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     DomType
  
   ￫ info[I0005]
   ￮ hole solved
  
   ￫ error[E1707]
   ￭ command line fake-interact
   1 | def K : DomType ≔ ? solve 0 ≔ data [ k. (_ : K) ] def kbad (u : ○ K) : ○ K ≔ match u [ circle. w ↦ match (w :○| _) [ k. y ↦ circle. (k. y) ] ]
     ^ window modality ○ must be pellucid since the datatype has recursive constructors
  

  $ narya -transparent-functor preserve.ny -fake-interact "def L : DomType ≔ ? solve 0 ≔ data [ l. ] def lgood (u : ○ L) : ○ L ≔ match u [ circle. w ↦ match (w :○| _) [ l. ↦ circle. (l.) ] ]"
   ￫ info[I0000]
   ￮ constant L defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     DomType
  
   ￫ info[I0005]
   ￮ hole solved
  
   ￫ info[I0000]
   ￮ constant lgood defined
  
