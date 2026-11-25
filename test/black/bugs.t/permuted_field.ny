{` A higher field projected with a nontrivial insertion from a neutral (here the ⁽³²¹⁾ on bA2.2 .lconn.2 in connectable_Br) used to get a type whose boundary normals carried the types of the wrong faces.  This showed up as a spurious boundary mismatch when a2.22, whose type comes from that projection, was used as a primary argument with synthesized implicit boundary. `}

def connectable (A : Type) : Type ≔ codata [
| c .lconn.p : Br (Br Type) (Br A.0) A.2 (Br A.0) A.2 ]

def gHasConn (A : Type) (b : connectable A) : Type ≔ codata [
| c .lconn.p
  : (a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1)
    → b.2 .lconn (rel a0) a2 (rel a0) a2 ]

def connectable_Br (A0 : Type) (A1 : Type) (A2 : Type⁽ᵖ⁾ A0 A1)
  (b0 : connectable A0) (b1 : connectable A1)
  (b2 : connectable⁽ᵖ⁾ A2 b0 b1) (c0 : gHasConn A0 b0)
  (c1 : gHasConn A1 b1) (a0 : A0) (a1 : A1)
  : connectable (A2 a0 a1)
  ≔ [
| .lconn.p ↦
    (b2.2 .lconn.2)⁽³²¹⁾ (sym (c0.2 .lconn a0.0 a0.1 a0.2))
      (sym (c1.2 .lconn a1.0 a1.1 a1.2)) ]

def connectableᵈ (A : Type) (B : A → Type) (bA : connectable A) : Type
  ≔ codata [
| bB .lconn.p
  : ((X ↦ X → Type) : Type → Type)⁽ᵖᵖ⁾ (bA.2 .lconn) (Br B.0) B.2 (Br B.0)
      B.2 ]

def gHasConnᵈ (A : Type) (B : A → Type) (bA : connectable A)
  (bB : connectableᵈ A B bA) (cA : gHasConn A bA)
  : Type
  ≔ codata [
| cB .lconn.p
  : (a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) (b0 : B.0 a0) (b1 : B.1 a1)
    (b2 : B.2 a2 b0 b1)
    → bB.2 .lconn (cA .lconn a0 a1 a2) (rel b0) b2 (rel b0) b2 ]

def connectableᵈ_Br (A0 : Type) (A1 : Type) (A2 : Type⁽ᵖ⁾ A0 A1)
  (B0 : A0 → Type) (B1 : A1 → Type)
  (B2 : {x0 : A0} {x1 : A1} (x2 : A2 x0 x1) →⁽ᵖ⁾ Type⁽ᵖ⁾ (B0 x0) (B1 x1))
  (bA0 : connectable A0) (bA1 : connectable A1)
  (bA2 : connectable⁽ᵖ⁾ A2 bA0 bA1) (bB0 : connectableᵈ A0 B0 bA0)
  (bB1 : connectableᵈ A1 B1 bA1) (bB2 : connectableᵈ⁽ᵖ⁾ A2 B2 bA2 bB0 bB1)
  (cA0 : gHasConn A0 bA0) (cA1 : gHasConn A1 bA1)
  (cB0 : gHasConnᵈ A0 B0 bA0 bB0 cA0) (cB1 : gHasConnᵈ A1 B1 bA1 bB1 cA1)
  (a0 : A0) (a1 : A1) (b0 : B0 a0) (b1 : B1 a1)
  : connectableᵈ (A2 a0 a1) (a2 ↦ B2 a2 b0 b1)
      (connectable_Br A0 A1 A2 bA0 bA1 bA2 cA0 cA1 a0 a1)
  ≔ [
| .lconn.p ↦ a2 ⤇
    (bB2.2 .lconn.2)⁽³²¹⁾ a2.22
      (sym (cB0.2 .lconn a0.0 a0.1 a0.2 b0.0 b0.1 b0.2))
      (sym (cB1.2 .lconn a1.0 a1.1 a1.2 b1.0 b1.1 b1.2)) ]
