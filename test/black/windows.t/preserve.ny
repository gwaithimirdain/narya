{` -*- narya-prog-args: ("-proofgeneral" "-functor") -*- `}

` A transparent modal operator preserves the empty type and binary disjoint
` unions, up to isomorphism.

def ○ (A :○| DomType) : CodType ≔ data [ circle. (_ :○| A) ]

` The empty type at each mode.

def ⊥ : DomType ≔ data [ ]

def ⊥' : CodType ≔ data [ ]

` Preservation of the empty type.  The forward map refutes the contents of the
` circle under the window modality ○.

def zfwd (u : ○ ⊥) : ⊥' ≔ match u [ circle. x ↦ match (x :○| _) [ ] ]

def zbwd (v : ⊥') : ○ ⊥ ≔ match v [ ]

def zbwd∘zfwd (u : ○ ⊥) : Id (○ ⊥) (zbwd (zfwd u)) u ≔ match u [
| circle. x ↦ match (x :○| _) [ ]]

def zfwd∘zbwd (v : ⊥') : Id ⊥' (zfwd (zbwd v)) v ≔ match v [ ]

` Binary disjoint unions at each mode.

def sum (A B : DomType) : DomType ≔ data [ inl. (_ : A) | inr. (_ : B) ]

def sum' (A B : CodType) : CodType ≔ data [ inl. (_ : A) | inr. (_ : B) ]

` Preservation of binary disjoint unions.  Since sum has two constructors, the
` forward map requires the window modality ○ to be transparent.

def sfwd (A B :○| DomType) (u : ○ (sum A B)) : sum' (○ A) (○ B) ≔ match u [
| circle. x ↦ match (x :○| _) [
  | inl. a ↦ inl. (circle. a)
  | inr. b ↦ inr. (circle. b)]]

def sbwd (A B :○| DomType) (v : sum' (○ A) (○ B)) : ○ (sum A B) ≔ match v [
| inl. p ↦ match p [ circle. a ↦ circle. (inl. a) ]
| inr. q ↦ match q [ circle. b ↦ circle. (inr. b) ]]

def sbwd∘sfwd (A B :○| DomType) (u : ○ (sum A B))
  : Id (○ (sum A B)) (sbwd A B (sfwd A B u)) u
  ≔ match u [
| circle. x ↦ match (x :○| _) [
  | inl. a ↦ refl (circle. (inl. a))
  | inr. b ↦ refl (circle. (inr. b))]]

def sfwd∘sbwd (A B :○| DomType) (v : sum' (○ A) (○ B))
  : Id (sum' (○ A) (○ B)) (sfwd A B (sbwd A B v)) v
  ≔ match v [
| inl. p ↦ match p [ circle. a ↦ refl (inl. (circle. a)) ]
| inr. q ↦ match q [ circle. b ↦ refl (inr. (circle. b)) ]]

` Some recursive datatypes, on whose contents ○ cannot be used as a window
` since it is transparent but not pellucid.

def ℕ : DomType ≔ data [ zero. | suc. (_ : ℕ) ]

def R : DomType ≔ data [ r. (_ : R) ]

` A mutual pair: X mentions its companion Y, so it is conservatively counted
` as recursive, but Y itself is not.

def X : DomType ≔ data [ x. (_ : Y) ]

and Y : DomType ≔ data [ y. ]

def ytest (u : ○ Y) : ○ Y ≔ match u [
| circle. w ↦ match (w :○| _) [ y. ↦ circle. (y.) ]]

` An occurrence only in the output type of a constructor, as for indexed
` families, is not recursive.

def V : ℕ → DomType ≔ data [ vnil. : V zero. ]

def vtest (u : ○ (V zero.)) : ○ (V zero.) ≔ match u [
| circle. w ↦ match (w :○| _) [ vnil. ↦ circle. (vnil.) ]]
