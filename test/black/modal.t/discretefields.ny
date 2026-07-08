{` -*- narya-prog-args: ("-proofgeneral" "-discrete-spatial") -*- `}

` In the discrete spatial mode theory, the left adjoint ♭ is *nonparametric*: it
` filters away the (single) parametric/reflexivity direction.  So a ♭-modal field
` "disappears" at any dimension it filters nontrivially — it cannot be projected
` there, and must be omitted from (not supplied in) a tuple/comatch at that
` dimension.

def N : Type ≔ data [ zero. | suc. (_ : N) ]

def C : Type ≔ codata [ (x :♭| _) .fld : N ]

def c : C ≔ [ .fld ↦ suc. zero. ]

` At dimension 0 the field is present: it projects and computes as usual.
def p : N ≔ (c :♭| _) .fld

def p_test : Id N p (suc. zero.) ≔ refl (suc. zero.)

` An ordinary (non-modal, identity-adjunction) field never disappears.
def D : Type ≔ codata [ y .snd : N ]

def d : D ≔ [ .snd ↦ zero. ]

` At dimension 1 the ♭-field disappears, so a comatch/tuple for a 1-dimensional
` element of C must OMIT it: the empty comatch suffices.
def cc : Id C c c ≔ [ ]
