  $ narya -hott hott.ny
  A₂ .trr.1
    : A₀ → A₁
  
  A₂ .trl.1
    : A₁ → A₀
  
  A₂ .liftr.1
    : (x₀ : A₀) → A₂ x₀ (A₂ .trr.1 x₀)
  
  A₂ .liftl.1
    : (x₁ : A₁) → A₂ (A₂ .trl.1 x₁) x₁
  
  A₂ .trr.1 a₀
    : A₁
  
  A₂ .liftr.1 a₀
    : A₂ a₀ (A₂ .trr.1 a₀)
  
  A₂ .trl.1 a₁
    : A₀
  
  A₂ .liftl.1 a₁
    : A₂ (A₂ .trl.1 a₁) a₁
  

  $ narya -hott hott2.ny
  A22 .trr.1
    : refl Π A02 {_ ↦ A10} {_ ↦ A11} (_ ⤇ A12) (A20 .trr.1) (A21 .trr.1)
  
  A22 .trr.1 a02
    : A12 (A20 .trr.1 a00) (A21 .trr.1 a01)
  
  A20 .trr.1 a00
    : A10
  
  A21 .trr.1 a01
    : A11
  
  A22 .liftr.1
    : refl Π A02 {x₀ ↦ A20 x₀ (A20 .trr.1 x₀)} {x₀ ↦ A21 x₀ (A21 .trr.1 x₀)}
        (x₀ ⤇ A22 x₀.2 (A22 .trr.1 x₀.2)) (A20 .liftr.1) (A21 .liftr.1)
  
  A22 .liftr.1 a02
    : A22 a02 (A22 .trr.1 a02) (A20 .liftr.1 a00) (A21 .liftr.1 a01)
  
  A20 .liftr.1 a00
    : A20 a00 (A20 .trr.1 a00)
  
  A21 .liftr.1 a01
    : A21 a01 (A21 .trr.1 a01)
  
  A22 .trl.1
    : refl Π A12 {_ ↦ A00} {_ ↦ A01} (_ ⤇ A02) (A20 .trl.1) (A21 .trl.1)
  
  A22 .trl.1 a12
    : A02 (A20 .trl.1 a10) (A21 .trl.1 a11)
  
  A20 .trl.1 a10
    : A00
  
  A21 .trl.1 a11
    : A01
  
  A22 .trr.2
    : refl Π A20 {_ ↦ A01} {_ ↦ A11} (_ ⤇ A21) (A02 .trr.1) (A12 .trr.1)
  
  A22 .trr.2 a20
    : A21 (A02 .trr.1 a00) (A12 .trr.1 a10)
  
  sym A22 .trr.1 a20
    : A21 (A02 .trr.1 a00) (A12 .trr.1 a10)
  
  A02 .trr.1 a00
    : A01
  
  A12 .trr.1 a10
    : A11
  
  A22 .liftr.2
    : refl Π A20 {x₀ ↦ A02 x₀ (A02 .trr.1 x₀)} {x₀ ↦ A12 x₀ (A12 .trr.1 x₀)}
        (x₀ ⤇ sym A22 x₀.2 (sym A22 .trr.1 x₀.2)) (A02 .liftr.1) (A12 .liftr.1)
  
  A22 .liftr.2 a20
    : sym A22 a20 (sym A22 .trr.1 a20) (A02 .liftr.1 a00) (A12 .liftr.1 a10)
  
  sym A22 .liftr.1 a20
    : sym A22 a20 (sym A22 .trr.1 a20) (A02 .liftr.1 a00) (A12 .liftr.1 a10)
  
  sym A22 .trr.1 a20
    : A21 (A02 .trr.1 a00) (A12 .trr.1 a10)
  
  A02 .trr.1 a00
    : A01
  
  A12 .trr.1 a10
    : A11
  
  A02 .liftr.1 a00
    : A02 a00 (A02 .trr.1 a00)
  
  A12 .liftr.1 a10
    : A12 a10 (A12 .trr.1 a10)
  
  A22 a02 a12 .trr.1
    : A20 a00 a10 → A21 a01 a11
  
  A22 a02 a12 .trr.1 a20
    : A21 a01 a11
  
  A22 a02 a12 .liftr.1 a20
    : A22 a02 a12 a20 (A22 a02 a12 .trr.1 a20)
  
  A22 a02 a12 .trl.1
    : A21 a01 a11 → A20 a00 a10
  
  A22 a02 a12 .trl.1 a21
    : A20 a00 a10
  
  A22 a02 a12 .liftl.1 a21
    : A22 a02 a12 (A22 a02 a12 .trl.1 a21) a21
  
  sym A22 a20 a21 .trr.1
    : A02 a00 a01 → A12 a10 a11
  
  sym A22 a20 a21 .trr.1 a02
    : A12 a10 a11
  
  sym (sym A22 a20 a21 .liftr.1 a02)
    : A22 a02 (sym A22 a20 a21 .trr.1 a02) a20 a21
  
  sym A22 a20 a21 .trl.1
    : A12 a10 a11 → A02 a00 a01
  
  sym A22 a20 a21 .trl.1 a12
    : A02 a00 a01
  
  sym (sym A22 a20 a21 .liftl.1 a12)
    : A22 (sym A22 a20 a21 .trl.1 a12) a12 a20 a21
  

  $ narya -hott -v J.ny
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
   ￫ info[I0100]
   ￮ option set type boundaries to implicit
  
   ￫ info[I0000]
   ￮ constant transport defined
  
   ￫ info[I0000]
   ￮ constant concat defined
  
   ￫ info[I0000]
   ￮ constant inverse defined
  
   ￫ info[I0000]
   ￮ constant transport2 defined
  
   ￫ info[I0000]
   ￮ constant refl_transport_1 defined
  
   ￫ info[I0000]
   ￮ constant refl_transport_2 defined
  
   ￫ info[I0000]
   ￮ constant Id2 defined
  
   ￫ info[I0000]
   ￮ constant concat_p1 defined
  
   ￫ info[I0000]
   ￮ constant J defined
  
   ￫ info[I0000]
   ￮ constant Sq defined
  
   ￫ info[I0000]
   ￮ constant conn defined
  
   ￫ info[I0000]
   ￮ constant coconn defined
  
   ￫ info[I0000]
   ￮ constant concat_1p defined
  
   ￫ info[I0000]
   ￮ constant Jβ defined
  

  $ narya -hott -v univalence.ny
   ￫ info[I0100]
   ￮ option set function boundaries to implicit
  
   ￫ info[I0100]
   ￮ option set type boundaries to implicit
  
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0000]
   ￮ constant isContr defined
  
   ￫ info[I0000]
   ￮ constant iscontr_idfrom defined
  
   ￫ info[I0000]
   ￮ constant is11 defined
  
   ￫ info[I0000]
   ￮ constant is11_Id defined
  
   ￫ info[I0000]
   ￮ constant bisim_of_11 defined
  
   ￫ info[I0000]
   ￮ constant univalence defined
  
