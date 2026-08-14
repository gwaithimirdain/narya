option modal ≔ spatial

def N : Type ≔ data [ zero. | suc. (_ : N) ]

` A codatatype with a ♭-modal field.  The left adjoint ♭ is sinister, with right
` adjoint ♯; so the field's type is checked in a context locked by ♯.
def C : Type ≔ codata [ (x :♭| _) .fld : N ]

` A comatch: the component is checked in a context locked by ♯.
def c : C ≔ [ .fld ↦ suc. zero. ]

` A projection is written with the locking left adjoint ♭ as an ascription.
def p : N ≔ (c :♭| _) .fld

` The projection computes: p ≡ suc. zero.
def p_test : Id N p (suc. zero.) ≔ refl (suc. zero.)

` A modal projection can be taken from a ♭-modal variable.
def proj (z :♭| C) : N ≔ (z :♭| _) .fld

def proj_test : Id N (proj c) (suc. zero.) ≔ refl (suc. zero.)

` A record (with eta) can have a modal field too, using self-variable syntax.
def R : Type ≔ sig ( (x :♭| _) .fst : N )

def r : R ≔ (fst ≔ zero.)

` Eta-conversion for a modal record field: any s : R equals the tuple of its
` (♭-keyed) projection.
def eta (s : R) : Id R s (fst ≔ (s :♭| _) .fst) ≔ refl s

` An ordinary (non-modal) field is the special case of the identity adjunction,
` and is projected with no annotation as usual.
def D : Type ≔ codata [ y .snd : N ]

def d : D ≔ [ .snd ↦ zero. ]

def d_test : Id N (d .snd) zero. ≔ refl zero.

` Parametrized negative modal operators
def ♯ (A :♯| Type) : Type ≔ sig ( (x :♭| _) .unsharp : A )

def ♯_unit (A :♯| Type) (x :♯| A) : ♯ A ≔ (unsharp ≔ x)

def ♯_mult (A :♯| Type) (x : ♯ (♯ A)) : ♯ A ≔ (
  unsharp ≔ ((x :♭| _) .unsharp :♭| _) .unsharp)

` The type of a modal field is checked in a context that is first locked by the
` right adjoint ♯ and then extended by the self variable, annotated by the left
` adjoint ♭.  Thus the self variable can be used in the types of later fields,
` projected under a ♭-lock as usual.
def C2 : Type ≔ codata [
| (x :♭| _) .fst : N
| (y :♭| _) .snd : Id N ((y :♭| _) .fst) ((y :♭| _) .fst) ]

def c2 : C2 ≔ [ .fst ↦ suc. zero. | .snd ↦ refl (suc. zero.) ]

def c2_test : Id N ((c2 :♭| _) .fst) (suc. zero.) ≔ refl (suc. zero.)

def c2_snd : Id N ((c2 :♭| _) .fst) ((c2 :♭| _) .fst) ≔ (c2 :♭| _) .snd

` The self variable is transported into the doubly-locked context along the
` adjunction unit, so a self-dependent modal field can be projected from a
` *variable* (whose modal key matters), not just from a constant.
def projsnd (z :♭| C2) : Id N ((z :♭| _) .fst) ((z :♭| _) .fst) ≔ (z :♭| _) .snd
