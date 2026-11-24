axiom C : Type
def T : Type := sig ( X : Type, q : Id (Id Type X X) (refl X) (refl X), s : Id (Id Type C C) (refl C) (refl C), t : Id (Id (Id Type X X) (refl X) (refl X)) q s)
def U (X : Type) : Type := sig ( q : Id (Id Type X X) (refl X) (refl X), s : Id (Id Type C C) (refl C) (refl C), t : Id (Id (Id Type X X) (refl X) (refl X)) q s)
