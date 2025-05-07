import "isfibrant"
import "bookhott"

option function boundaries ≔ implicit
option type boundaries ≔ implicit

{` Facts about the interaction of Book HoTT equivalences (regarded as the outer 2LTT layer) and HOTT identity types. `}

{` An Id of equalities induces an equality involving transport `}
def Id_eq (A0 A1 : Type) (A2 : Id Type A0 A1) (a00 : A0) (a01 : A1)
  (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
  (a22 : Id eq A2 a02 a12 a20 a21)
  : eq (A2 a10 a11)
      (eq.trr2 A0 A1 (x y ↦ A2 x y) a00 a10 a20 a01 a11 a21 a02) a12
  ≔ match a22 [ rfl. ⤇ rfl. ]

{` An Id of equivalences induces an equivalence on Ids. `}
def Id_eqv (A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : Type)
  (B1 : Type) (B2 : Id Type B0 B1) (e0 : A0 ≅ B0) (e1 : A1 ≅ B1)
  (e2 : Id eqv A2 B2 e0 e1) (b0 : B0) (b1 : B1)
  : A2 (e0 .fro b0) (e1 .fro b1) ≅ B2 b0 b1
  ≔
  let f0 ≔ e0 .to in
  let g0 ≔ e0 .fro in
  let ap_g0 ≔ eq.ap B0 A0 g0 in
  let fg0 : B0 → B0 ≔ x ↦ f0 (g0 x) in
  let gfg0 : B0 → A0 ≔ x ↦ g0 (f0 (g0 x)) in
  let ε0 ≔ e0 .to_fro in
  let η0 ≔ e0 .fro_to in
  let f1 ≔ e1 .to in
  let g1 ≔ e1 .fro in
  let ap_g1 ≔ eq.ap B1 A1 g1 in
  let fg1 : B1 → B1 ≔ x ↦ f1 (g1 x) in
  let gfg1 : B1 → A1 ≔ x ↦ g1 (f1 (g1 x)) in
  let ε1 ≔ e1 .to_fro in
  let η1 ≔ e1 .fro_to in
  let f2 ≔ e2 .to in
  let g2 ≔ e2 .fro in
  let η2 ≔ e2 .fro_to in
  let ε2 ≔ e2 .to_fro in
  adjointify (A2 (g0 b0) (g1 b1)) (B2 b0 b1)
    (a2 ↦
     eq.trr2 B0 B1 (b0 b1 ↦ B2 b0 b1) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1 (ε1 b1)
       (f2 a2)) (b2 ↦ g2 b2)
    (a2 ↦
     eq.cat (A2 (g0 b0) (g1 b1))
       (g2
          (eq.trr2 B0 B1 (x y ↦ B2 x y) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1
             (ε1 b1) (f2 a2)))
       (eq.trr2 A0 A1 (x y ↦ A2 x y) (gfg0 b0) (g0 b0)
          (ap_g0 (fg0 b0) b0 (ε0 b0)) (gfg1 b1) (g1 b1)
          (ap_g1 (fg1 b1) b1 (ε1 b1)) (g2 (f2 a2))) a2
       (eq.trr2_ap B0 B1 (x y ↦ B2 x y) A0 A1 (x y ↦ A2 x y) g0 g1
          (x0 x1 x2 ↦ g2 x2) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1 (ε1 b1) (f2 a2))
       (Id_eq A0 A1 A2 (gfg0 b0) (gfg1 b1) (g2 (f2 a2)) (g0 b0) (g1 b1) a2
          (ap_g0 (fg0 b0) b0 (ε0 b0)) (ap_g1 (fg1 b1) b1 (ε1 b1))
          (eq.trl2 (eq A0 (gfg0 b0) (g0 b0)) (eq A1 (gfg1 b1) (g1 b1))
             (u v ↦ Id eq A2 (g2 (f2 a2)) a2 u v) (ap_g0 (fg0 b0) b0 (ε0 b0))
             (η0 (g0 b0)) (fro_to_fro A0 B0 e0 b0)
             (ap_g1 (fg1 b1) b1 (ε1 b1)) (η1 (g1 b1))
             (fro_to_fro A1 B1 e1 b1) (η2 a2))))
    (b2 ↦
     Id_eq B0 B1 B2 (fg0 b0) (fg1 b1) (f2 (g2 b2)) b0 b1 b2 (ε0 b0) (ε1 b1)
       (ε2 b2))

{` Fibrancy transports across equivalences. `}
def 𝕗eqv (A B : Type) (e : A ≅ B) (𝕗A : isFibrant A) : isFibrant B ≔ [
| .trr.e ↦ b0 ↦ e.1 .to (𝕗A.2 .trr.1 (e.0 .fro b0))
| .trl.e ↦ b1 ↦ e.0 .to (𝕗A.2 .trl.1 (e.1 .fro b1))
| .liftr.e ↦ b0 ↦
    eq.trr B.0 (b ↦ B.2 b (e.1 .to (𝕗A.2 .trr.1 (e.0 .fro b0))))
      (e.0 .to (e.0 .fro b0)) b0 (e.0 .to_fro b0)
      (e.2 .to (𝕗A.2 .liftr.1 (e.0 .fro b0)))
| .liftl.e ↦ b1 ↦
    eq.trr B.1 (b ↦ B.2 (e.0 .to (𝕗A.2 .trl.1 (e.1 .fro b1))) b)
      (e.1 .to (e.1 .fro b1)) b1 (e.1 .to_fro b1)
      (e.2 .to (𝕗A.2 .liftl.1 (e.1 .fro b1)))
| .id.e ↦ b0 b1 ↦
    𝕗eqv (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
      (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)
      (𝕗A.2 .id.1 (e.0 .fro b0) (e.1 .fro b1))]

{` Symmetry is an equivalence `}
def sym_eqv (A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
  (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
  (A22 : Id (Id Type) A02 A12 A20 A21) (a00 : A00) (a01 : A01)
  (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
  (a20 : A20 a00 a10) (a21 : A21 a01 a11)
  : A22 a02 a12 a20 a21 ≅ sym A22 a20 a21 a02 a12
  ≔ (
  to ≔ a22 ↦ sym a22,
  fro ≔ a22 ↦ sym a22,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)

def 312_eqv (A000 : Type) (A001 : Type) (A002 : Id Type A000 A001)
  (A010 : Type) (A011 : Type) (A012 : Id Type A010 A011)
  (A020 : Id Type A000 A010) (A021 : Id Type A001 A011)
  (A022 : Id (Id Type) A002 A012 A020 A021)
  {` Top face `}
  (A100 : Type) (A101 : Type) (A102 : Id Type A100 A101) (A110 : Type)
  (A111 : Type) (A112 : Id Type A110 A111) (A120 : Id Type A100 A110)
  (A121 : Id Type A101 A111) (A122 : Id (Id Type) A102 A112 A120 A121)
  {` Front face `}
  (A200 : Id Type A000 A100) (A201 : Id Type A001 A101)
  (A202 : Id (Id Type) A002 A102 A200 A201)
  {` Back face `}
  (A210 : Id Type A010 A110) (A211 : Id Type A011 A111)
  (A212 : Id (Id Type) A012 A112 A210 A211)
  {` Left face `}
  (A220 : Id (Id Type) A020 A120 A200 A210)
  {` Right face `}
  (A221 : Id (Id Type) A021 A121 A201 A211)
  {` Center `}
  (A222 : Id (Id (Id Type)) A022 A122 A202 A212 A220 A221) (a000 : A000)
  (a001 : A001) (a002 : A002 a000 a001) (a010 : A010) (a011 : A011)
  (a012 : A012 a010 a011) (a020 : A020 a000 a010) (a021 : A021 a001 a011)
  (a022 : A022 a002 a012 a020 a021)
  {` Top face `}
  (a100 : A100) (a101 : A101) (a102 : A102 a100 a101) (a110 : A110)
  (a111 : A111) (a112 : A112 a110 a111) (a120 : A120 a100 a110)
  (a121 : A121 a101 a111) (a122 : A122 a102 a112 a120 a121)
  {` Front face `}
  (a200 : A200 a000 a100) (a201 : A201 a001 a101)
  (a202 : A202 a002 a102 a200 a201)
  {` Back face `}
  (a210 : A210 a010 a110) (a211 : A211 a011 a111)
  (a212 : A212 a012 a112 a210 a211)
  {` Left face `}
  (a220 : A220 a020 a120 a200 a210)
  {` Right face `}
  (a221 : A221 a021 a121 a201 a211)
  : A222 a022 a122 a202 a212 a220 a221
    ≅ A222⁽³¹²⁾ a220 a221 (sym a022) (sym a122) (sym a202) (sym a212)
  ≔ (
  to ≔ a222 ↦ a222⁽³¹²⁾,
  fro ≔ a222 ↦ a222⁽²³¹⁾,
  to_fro ≔ _ ↦ rfl.,
  fro_to ≔ _ ↦ rfl.,
  to_fro_to ≔ _ ↦ rfl.)
