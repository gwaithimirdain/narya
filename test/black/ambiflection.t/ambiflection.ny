{` -*- narya-prog-args: ("-proofgeneral" "-ambiflection") -*- `}

` The unit of △ ⊣ □: a plain Disc value can supply a □△-locked field.
def □△ (A : Disc) : Disc ≔ data [ t. (_ :□△| A) ]

def eta (A : Disc) (x : A) : □△ A ≔ t. x

` The counit of □ ⊣ △ is, together with the unit of △ ⊣ □, an isomorphism □△ ≅ 1_Disc: a
` □△-locked variable can also be used directly.
def eta_inv (A : Disc) (x :□△| A) : A ≔ x

` The doubled composite □△□△ ⇒ 1_Disc is unique (there is only one normal form □△ ≅ 1_Disc
` collapses to).
def eta_inv2 (A : Disc) (x :□△□△| A) : A ≔ x

` The counit of △ ⊣ □: a △□-locked variable can be used directly.
def counit (A :△□| Type) (x :△□| A) : A ≔ x

` The unit of □ ⊣ △: a plain value can supply a △□-locked field.
def tribox : Type ≔ data [ u. (_ :△□| Type) ]

def wu (x : Type) : tribox ≔ u. x

` Unlike an ordinary reflector or coreflector alone, △□ having both a unit and a counit means
` every pair of {id, △□} normal forms has a key in both directions, so there is no analogue of
` the usual "missing key" test here.  But the two composites of the unit and counit are
` genuinely different, and this is directly observable, just as for ♮ in Ambiflector.

` Composing the counit and then the unit, △□ ⇒ id ⇒ △□, is the identity on △□: bouncing an
` already-△□ value out to a plain value and back through counit again reduces to the original
` counit.
def roundtrip_good (A :△□| Type) (x :△□| A) : A ≔ counit A (counit A x)

def roundtrip_good_ok (A :△□| Type) (x :△□| A)
  : Id A (roundtrip_good A x) x
  ≔ refl x

` Composing the unit and then the counit, id ⇒ △□ ⇒ id, is *not* the identity on id (it is
` "zero"): applying counit to a genuinely plain (unkeyed) value, which needs the unit inserted to
` supply counit's △□-locked argument, does not typecheck.
` def roundtrip_bad (A : Type) (x : A) : A ≔ counit A x

` △ is sinister (△ ⊣ □), so it can parametrize a modal (negative) field.
def □ (A :□| Type) : Disc ≔ codata [ (x :△| _) .unbox : A ]

def box (A :□| Type) (a :□| A) : □ A ≔ [ .unbox ↦ a ]

def unbox (A :△□| Type) (u :△| □ A) : A ≔ (u :△| _) .unbox

` unbox (box a) reduces to a, with the (unique) counit key applied.
def unbox_box (A :△□| Type) (a :△□| A) : Id A (unbox A (box A a)) a
  ≔ refl a

` □ is sinister (□ ⊣ △), so it can parametrize a modal (negative) field, this time on Disc.
def △ (A :△| Disc) : Type ≔ codata [ (x :□| _) .untri : A ]

def tri (A :△| Disc) (a :△| A) : △ A ≔ [ .untri ↦ a ]

def untri (A :□△| Disc) (u :□| △ A) : A ≔ (u :□| _) .untri

def untri_tri (A :□△| Disc) (a :□△| A) : Id A (untri A (tri A a)) a
  ≔ refl a

` The zero map
def zero (A : Type) (a : A) : A #ø ≔ a #ø

def zero△□ (A :△□| Type) (a : A) : A ≔ a #ø
