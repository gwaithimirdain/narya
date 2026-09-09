{` -*- narya-prog-args: ("-proofgeneral" "-discrete-spatial" "-parametric") -*- `}

` In the discrete spatial mode theory, the left adjoint ♭ is *nonparametric*: it
` filters away the (single) parametric/reflexivity direction.  So a ♭-modal field
` "disappears" at any dimension it filters nontrivially — it cannot be projected
` there, and must be omitted from (not supplied in) a tuple/comatch at that
` dimension.

def N : Type ≔ data [ zero. | suc. (_ : N) ]

def C : Type ≔ codata [ (x :♭| _) .fld : N ]

def c : C ≔ [ .fld ↦ suc. zero. ]
def c2 : C ≔ [ .fld ↦ suc. (suc. zero.) ]

` At dimension 0 the field is present: it projects and computes as usual.
def p : N ≔ (c :♭| _) .fld

def p_test : Id N p (suc. zero.) ≔ refl (suc. zero.)

` An ordinary (non-modal, identity-adjunction) field never disappears.
def D : Type ≔ codata [ y .snd : N ]

def d : D ≔ [ .snd ↦ zero. ]

` At dimension 1 the ♭-field disappears, so a comatch/tuple for a 1-dimensional
` element of C must OMIT it: the empty comatch suffices.
def cc : Id C c c2 ≔ [ ]

` The same for records, whose bridge types additionally have eta.
def ♯ (A : Type) : Type ≔ sig #(transparent positional) ( (x :♭| _) .unsharp : A )

axiom A : Type
axiom a0 : ♯ A
axiom a1 : ♯ A
def a2 : Id (♯ A) a0 a1 ≔ ()
axiom a20 : Id (♯ A) a0 a1
axiom a21 : Id (♯ A) a0 a1

` Because [Id (♯ A) a0 a1] is a record with no fields, any two of its elements are *definitionally* equal.
def a22 : Id (Id (♯ A) a0 a1) a20 a21 ≔ refl _
