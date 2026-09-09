{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-transparent-functor") -*- `}

def Gel (A B : DomType) (R : A → B → DomType) : Id DomType A B
  ≔ sig (
  a .ungel : R a.0 a.1 )

def ⊥ : DomType ≔ data []

def ⊤ : DomType ≔ sig ()

def ⊤eq⊥ : Id DomType ⊤ ⊥ ≔ Gel ⊤ ⊥ [ ]

def ○ (A :○| DomType) : CodType ≔ data [ circ. (_ :○| A) ]

def foo : ((_ :○| ⊤eq⊥) ⇒ refl (○ DomType)) (x ↦ circ. DomType) (x ↦ circ. DomType) ≔ [ ]
