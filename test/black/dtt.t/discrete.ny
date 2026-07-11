{` -*- narya-prog-args: ("-proofgeneral" "-dtt") -*- `}

{` A hack to access display of △□-annotated variables. `}

def disp (X :△□| Type) (x : X) : Type
  ≔ ((Y ↦ Y) : ((_ :△□| Type) → Type))⁽ᵈ⁾ X x

{` Martin-Löf equality `}

def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]

{` △, □, and △□ can be negative modalities, since they are right adjoints. `}
def △ (A :△| Disc) : Type ≔ sig ( (x :◇| _) .untri : A )

def □ (A :□| Type) : Disc ≔ sig ( (x :△| _) .unsq : A )

def △□ (A :△□| Type) : Type ≔ sig ( (x :△◇| _) .untrisq : A )

{` They are nonparametric, so △ and △□ have trivial display, definitionally. `}
def △ᵈ (A :△| Disc) (a : △ A) : disp (△ A) a ≔ ()

def △ᵈ_eq (A :△| Disc) (a00 : △ A) (a01 a10 : disp (△ A) a00)
  : eq (disp (△ A) a00) a01 a10
  ≔ rfl.

def △□ᵈ (A :△□| Type) (a : △□ A) : disp (△□ A) a ≔ ()
 
def △□ᵈ_eq (A :△□| Type) (a00 : △□ A) (a01 a10 : disp (△□ A) a00)
  : eq (disp (△□ A) a00) a01 a10
  ≔ rfl.

{` Unlike in the dTT paper, however, ◇ and △◇ cannot be negative modalities, since they are only p.r.a. and Narya requires full adjunctions.  But we can make them positive modalities. `}

def ◇ (A :◇| Type) : Disc ≔ data [ dia. (_ :◇| A) ]

def △◇ (A :△◇| Type) : Type ≔ data [ tridia. (_ :△◇| A) ]

{` They are also nonparametric, so △◇ also has trivial display, but not definitionally.  Note that we can write [(△◇ A)⁽ᵈ⁾] because △□ ∘ △◇ = △◇, which is the annotation on A. `}

def △◇ᵈ (A :△◇| Type) (a : △◇ A) : disp (△◇ A) a ≔ match a [
| tridia. x ↦ tridia. x]

def △◇ᵈ_eq (A :△◇| Type) (a0 : △◇ A) (a1 : disp (△◇ A) a0)
  : eq (disp (△◇ A) a0) a1 (△◇ᵈ A a0)
  ≔ match a1 [ tridia. a0 ⤇ rfl. ]
