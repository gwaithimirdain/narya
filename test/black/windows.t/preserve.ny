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
