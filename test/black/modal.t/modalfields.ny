{` -*- narya-prog-args: ("-proofgeneral" "-spatial") -*- `}

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
