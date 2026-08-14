option parametric ≔ arity 2, letter p, name rel Br
option modal ≔ transparent functor

def Gel (A B : DomType) (R : A → B → DomType) : Br DomType A B
  ≔ sig (
  a .ungel : R a.0 a.1 )

def ⊥ : DomType ≔ data []

def ⊤ : DomType ≔ sig ()

def ⊤eq⊥ : Br DomType ⊤ ⊥ ≔ Gel ⊤ ⊥ [ ]

def ○ (A :○| DomType) : CodType ≔ data [ circ. (_ :○| A) ]

def foo : ((_ :○| ⊤eq⊥) ⇒ rel (○ DomType)) (x ↦ circ. DomType) (x ↦ circ. DomType) ≔ [ ]
