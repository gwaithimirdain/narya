axiom A : Type
axiom a00 : A
axiom a01 : A
axiom a02 : Id A a00 a01
axiom a10 : A
axiom a11 : A
axiom a12 : Id A a10 a11
axiom a20 : Id A a00 a10
axiom a21 : Id A a01 a11
axiom a22 : refl (Id A) a02 a12 a20 a21

axiom B : Type
axiom b00 : B
axiom b01 : B
axiom b02 : Id B b00 b01
axiom b10 : B
axiom b11 : B
axiom b12 : Id B b10 b11
axiom b20 : Id B b00 b10
axiom b21 : Id B b01 b11
axiom b22 : refl (Id B) b02 b12 b20 b21

def prod (X Y : Type) : Type ≔ sig ( fst : X, snd : Y )

def ab22
  : Id (Id (prod A B)) {(a00, b00)} {(a01, b01)} (a02, b02) {(a10, b10)}
      {(a11, b11)} (a12, b12) (a20, b20) (a21, b21)
  ≔ (a22, b22)

def sym_ab22
  : Id (Id (prod A B)) {(a00, b00)} {(a10, b10)} (a20, b20) {(a01, b01)}
      {(a11, b11)} (a21, b21) (a02, b02) (a12, b12)
  ≔ (sym a22, sym b22)

{` This one requires symmetry to check in addition to synthesize, although it could also work with degeneracies applied to tuples. `}
def sym_ab22'
  : Id (Id (prod A B)) {(a00, b00)} {(a10, b10)} (a20, b20) {(a01, b01)}
      {(a11, b11)} (a21, b21) (a02, b02) (a12, b12)
  ≔ sym (a22, b22)

{` To make sure we're testing that symmetry checks, we do one with abstractions too, which degeneracies don't push through. `}

axiom f00 : A → B
axiom f01 : A → B
axiom f02 : Id (A → B) f00 f01
axiom f10 : A → B
axiom f11 : A → B
axiom f12 : Id (A → B) f10 f11
axiom f20 : Id (A → B) f00 f10
axiom f21 : Id (A → B) f01 f11
axiom f22 : Id (Id (A → B)) f02 f12 f20 f21

def etaf22 : Id (Id (A → B)) f02 f12 f20 f21 ≔ (x ⤇ f22 x.22)
def eta_symf22 : Id (Id (A → B)) f20 f21 f02 f12 ≔ (x ⤇ sym (f22 (sym x.22)))

def eta_symf22' : Id (Id (A → B)) f20 f21 f02 f12 ≔ sym (x ⤇ f22 x.22)
