{` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-nonparametric-comonad") -*- `}

` The modality ♭ is a *nonparametric* comonad: working under a ♭ lock filters
` out the parametric dimensions.  We set up the usual comonad structure, plus a
` non-modal type family T for contrast with the modal family ♭T.

def f (A : ♭| Type) (x : ♭| A) : A ≔ x

def ♭T (A : ♭| Type) : Type ≔ data [ box. (x : ♭| A) ]

def ♭map (A B : ♭| Type) (g : ♭| A → B) : ♭T A → ♭T B ≔ [ box. x ↦ box. (g x) ]

def ε (A : ♭| Type) (u : ♭T A) : A ≔ match u [ box. x ↦ x ]

def △ (A : ♭| Type) (u : ♭T A) : ♭T (♭T A) ≔ match u [ box. x ↦ box. (box. x) ]

` A non-modal family, whose refl has an unfiltered (square) domain.
def T (A : Type) : Type ≔ data [ mk. (x : A) ]
