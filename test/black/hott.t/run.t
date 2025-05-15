  $ narya -hott tr.ny
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
  

  $ narya -hott tr2.ny
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
  

  $ narya -hott pi.ny
  B₂ (A₂ .liftl.1 a₁) .trr.1 (f₀ (A₂ .trl.1 a₁))
    : B₁ a₁
  
  B₂ (A₂ .liftl.1 a₁) .trr.1 (f₀ (A₂ .trl.1 a₁))
    : B₁ a₁
  
  B₂ (A₂ .liftr.1 a₀) .trl.1 (f₁ (A₂ .trr.1 a₀))
    : B₀ a₀
  
  B₂ (A₂ .liftr.1 a₀) .trl.1 (f₁ (A₂ .trr.1 a₀))
    : B₀ a₀
  
  B₂⁽¹ᵉ⁾ (sym (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftl.1 a₁) .liftl.1 (refl a₁)))
      (refl f₀ (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftl.1 a₁) .trl.1 (refl a₁)))
      (B₂⁽¹ᵉ⁾ (A₂⁽¹ᵉ⁾ .liftl.1 (refl a₁))
       .trr.1 (refl f₀ (A₂⁽¹ᵉ⁾ .trl.1 (refl a₁))))
    .trl.1 (B₂ (A₂ .liftl.1 a₁) .liftr.1 (f₀ (A₂ .trl.1 a₁)))
    : B₂ a₂ (f₀ a₀) (B₂ (A₂ .liftl.1 a₁) .trr.1 (f₀ (A₂ .trl.1 a₁)))
  
  B₂⁽¹ᵉ⁾ (sym (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftl.1 a₁) .liftl.1 (refl a₁)))
      (refl f₀ (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftl.1 a₁) .trl.1 (refl a₁)))
      (B₂⁽¹ᵉ⁾ (A₂⁽¹ᵉ⁾ .liftl.1 (refl a₁))
       .trr.1 (refl f₀ (A₂⁽¹ᵉ⁾ .trl.1 (refl a₁))))
    .trl.1 (B₂ (A₂ .liftl.1 a₁) .liftr.1 (f₀ (A₂ .trl.1 a₁)))
    : B₂ a₂ (f₀ a₀) (B₂ (A₂ .liftl.1 a₁) .trr.1 (f₀ (A₂ .trl.1 a₁)))
  
  B₂⁽¹ᵉ⁾ (sym (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftr.1 a₀) .liftr.1 (refl a₀)))
      (B₂⁽¹ᵉ⁾ (A₂⁽¹ᵉ⁾ .liftr.1 (refl a₀))
       .trl.1 (refl f₁ (A₂⁽¹ᵉ⁾ .trr.1 (refl a₀))))
      (refl f₁ (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftr.1 a₀) .trr.1 (refl a₀)))
    .trl.1 (B₂ (A₂ .liftr.1 a₀) .liftl.1 (f₁ (A₂ .trr.1 a₀)))
    : B₂ a₂ (B₂ (A₂ .liftr.1 a₀) .trl.1 (f₁ (A₂ .trr.1 a₀))) (f₁ a₁)
  
  B₂⁽¹ᵉ⁾ (sym (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftr.1 a₀) .liftr.1 (refl a₀)))
      (B₂⁽¹ᵉ⁾ (A₂⁽¹ᵉ⁾ .liftr.1 (refl a₀))
       .trl.1 (refl f₁ (A₂⁽¹ᵉ⁾ .trr.1 (refl a₀))))
      (refl f₁ (A₂⁽ᵉ¹⁾ a₂ (A₂ .liftr.1 a₀) .trr.1 (refl a₀)))
    .trl.1 (B₂ (A₂ .liftr.1 a₀) .liftl.1 (f₁ (A₂ .trr.1 a₀)))
    : B₂ a₂ (B₂ (A₂ .liftr.1 a₀) .trl.1 (f₁ (A₂ .trr.1 a₀))) (f₁ a₁)
  

  $ narya -hott pi2.ny
  B22 (A22 (A02 .liftl.1 a01) (A12 .liftl.1 a11) .liftl.1 a21)
      (f02 (A02 .liftl.1 a01)) (f12 (A12 .liftl.1 a11))
    .trr.1 (f20 (A22 (A02 .liftl.1 a01) (A12 .liftl.1 a11) .trl.1 a21))
    : B21 a21 (f01 a01) (f11 a11)
  
  B22 (A22 (A02 .liftl.1 a01) (A12 .liftl.1 a11) .liftl.1 a21)
      (f02 (A02 .liftl.1 a01)) (f12 (A12 .liftl.1 a11))
    .trr.1 (f20 (A22 (A02 .liftl.1 a01) (A12 .liftl.1 a11) .trl.1 a21))
    : B21 a21 (f01 a01) (f11 a11)
  
  B22 (A22 (A02 .liftr.1 a00) (A12 .liftr.1 a10) .liftr.1 a20)
      (f02 (A02 .liftr.1 a00)) (f12 (A12 .liftr.1 a10))
    .trl.1 (f21 (A22 (A02 .liftr.1 a00) (A12 .liftr.1 a10) .trr.1 a20))
    : B20 a20 (f00 a00) (f10 a10)
  
  B22 (A22 (A02 .liftr.1 a00) (A12 .liftr.1 a10) .liftr.1 a20)
      (f02 (A02 .liftr.1 a00)) (f12 (A12 .liftr.1 a10))
    .trl.1 (f21 (A22 (A02 .liftr.1 a00) (A12 .liftr.1 a10) .trr.1 a20))
    : B20 a20 (f00 a00) (f10 a10)
  
  B22⁽¹²ᵉ⁾
      (A22⁽¹²ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01) .liftl.1 (refl a01)))
           (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10) (refl A11 .liftr.1 a11)
            .liftr.1 a12)
           (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01) .trl.1 (refl a01))
                (refl A10 .liftr.1 a10)
            .liftr.1 a20)
           (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .liftr.1 a21)
       .liftr.1 a22)
      (f02⁽¹ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01) .liftl.1 (refl a01))))
      (f12⁽¹ᵉ⁾
         (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10) (refl A11 .liftr.1 a11) .liftr.1 a12))
      (refl f20
         (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01) .trl.1 (refl a01))
              (refl A10 .liftr.1 a10)
          .liftr.1 a20))
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01))
                (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr.1 a11))
            .liftl.1 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .liftr.1 a21))
           (f02⁽¹ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01)))
           (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr.1 a11)))
       .trr.1
         (refl f20
            (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01))
                 (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr.1 a11))
             .trl.1 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .liftr.1 a21))))
    .trl.1
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                (sym
                   (A12⁽ᵉ¹⁾
                        (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                             (refl A11 .liftr.1 a11)
                         .trr.1 a12) (A12 .liftl.1 (refl A11 .trr.1 a11))
                    .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                     (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                               (refl A11 .liftr.1 a11)
                           .trr.1 a12) (A12 .liftl.1 (refl A11 .trr.1 a11))
                      .trl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                 .liftr.1
                   (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01) .trl.1 (refl a01))
                        (refl A10 .liftr.1 a10)
                    .trr.1 a20))
                (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                 .liftr.1
                   (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .trr.1 a21))
            .liftr.1
              (A22⁽¹²ᵉ⁾
                   (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01) .liftl.1 (refl a01)))
                   (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10) (refl A11 .liftr.1 a11)
                    .liftr.1 a12)
                   (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01) .trl.1 (refl a01))
                        (refl A10 .liftr.1 a10)
                    .liftr.1 a20)
                   (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .liftr.1 a21)
               .trr.1 a22)) (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
           (f12⁽¹ᵉ⁾
              (sym
                 (A12⁽ᵉ¹⁾
                      (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10) (refl A11 .liftr.1 a11)
                       .trr.1 a12) (A12 .liftl.1 (refl A11 .trr.1 a11))
                  .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))))
           (refl f20
              (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                   (A12⁽ᵉ¹⁾
                        (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                             (refl A11 .liftr.1 a11)
                         .trr.1 a12) (A12 .liftl.1 (refl A11 .trr.1 a11))
                    .trl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
               .liftr.1
                 (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01) .trl.1 (refl a01))
                      (refl A10 .liftr.1 a10)
                  .trr.1 a20)))
           (B22⁽¹²ᵉ⁾
                (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                     (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                 .liftl.1
                   (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                    .liftr.1
                      (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .trr.1 a21)))
                (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
                (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
            .trr.1
              (refl f20
                 (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                      (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                  .trl.1
                    (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                     .liftr.1
                       (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .trr.1 a21)))))
       .trl.1
         (B22⁽¹²ᵉ⁾
              (sym
                 (A22⁽ᵉ¹⁾ (sym (refl A02 .liftl.1 (refl a01)))
                      (sym (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                      (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                           (sym
                              (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                        (refl A11 .liftr.1 a11)
                                    .trr.1 a12)
                                   (A12 .liftl.1 (refl A11 .trr.1 a11))
                               .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                           (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                                (A12⁽ᵉ¹⁾
                                     (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                          (refl A11 .liftr.1 a11)
                                      .trr.1 a12)
                                     (A12 .liftl.1 (refl A11 .trr.1 a11))
                                 .trl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                            .liftr.1
                              (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01)
                                    .trl.1 (refl a01)) (refl A10 .liftr.1 a10)
                               .trr.1 a20))
                           (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                            .liftr.1
                              (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11)
                               .trr.1 a21))
                       .trr.1
                         (A22⁽¹²ᵉ⁾
                              (sym
                                 (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01)
                                  .liftl.1 (refl a01)))
                              (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                   (refl A11 .liftr.1 a11)
                               .liftr.1 a12)
                              (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01)
                                    .trl.1 (refl a01)) (refl A10 .liftr.1 a10)
                               .liftr.1 a20)
                              (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11)
                               .liftr.1 a21)
                          .trr.1 a22))
                      (A22 (A02 .liftl.1 a01)
                           (A12 .liftl.1 (refl A11 .trr.1 a11))
                       .liftl.1
                         (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                          .trr.1
                            (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11)
                             .trr.1 a21)))
                  .liftl.1
                    (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                     .trr.1
                       (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                        .trr.1 (refl a21)))))
              (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
              (f12⁽¹ᵉ⁾ (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
              (refl f20
                 (A22⁽ᵉ¹⁾ (sym (refl A02 .liftl.1 (refl a01)))
                      (sym (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                      (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                           (sym
                              (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                        (refl A11 .liftr.1 a11)
                                    .trr.1 a12)
                                   (A12 .liftl.1 (refl A11 .trr.1 a11))
                               .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                           (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                                (A12⁽ᵉ¹⁾
                                     (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                          (refl A11 .liftr.1 a11)
                                      .trr.1 a12)
                                     (A12 .liftl.1 (refl A11 .trr.1 a11))
                                 .trl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                            .liftr.1
                              (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01)
                                    .trl.1 (refl a01)) (refl A10 .liftr.1 a10)
                               .trr.1 a20))
                           (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                            .liftr.1
                              (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11)
                               .trr.1 a21))
                       .trr.1
                         (A22⁽¹²ᵉ⁾
                              (sym
                                 (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01)
                                  .liftl.1 (refl a01)))
                              (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                   (refl A11 .liftr.1 a11)
                               .liftr.1 a12)
                              (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftl.1 a01)
                                    .trl.1 (refl a01)) (refl A10 .liftr.1 a10)
                               .liftr.1 a20)
                              (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11)
                               .liftr.1 a21)
                          .trr.1 a22))
                      (A22 (A02 .liftl.1 a01)
                           (A12 .liftl.1 (refl A11 .trr.1 a11))
                       .liftl.1
                         (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                          .trr.1
                            (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11)
                             .trr.1 a21)))
                  .trl.1
                    (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                     .trr.1
                       (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                        .trr.1 (refl a21)))))
              (B22⁽¹²ᵉ⁾
                   (A22⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                        (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                    .liftl.1
                      (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                       .trr.1
                         (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                          .trr.1 (refl a21))))
                   (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
                   (f12⁽¹ᵉ⁾ (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
               .trr.1
                 (refl f20
                    (A22⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                         (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                     .trl.1
                       (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                        .trr.1
                          (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                           .trr.1 (refl a21))))))
          .trl.1
            (B22
                 (A22 (A02 .liftl.1 a01) (A12 .liftl.1 (refl A11 .trr.1 a11))
                  .liftl.1
                    (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                     .trr.1
                       (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .trr.1 a21)))
                 (f02 (A02 .liftl.1 a01))
                 (f12 (A12 .liftl.1 (refl A11 .trr.1 a11)))
             .liftr.1
               (f20
                  (A22 (A02 .liftl.1 a01) (A12 .liftl.1 (refl A11 .trr.1 a11))
                   .trl.1
                     (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                      .trr.1
                        (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr.1 a11) .trr.1 a21)))))))
    : B22 a22 (f02 a02) (f12 a12) (f20 a20)
        (B22 (A22 (A02 .liftl.1 a01) (A12 .liftl.1 a11) .liftl.1 a21)
             (f02 (A02 .liftl.1 a01)) (f12 (A12 .liftl.1 a11))
         .trr.1 (f20 (A22 (A02 .liftl.1 a01) (A12 .liftl.1 a11) .trl.1 a21)))
  
  B22⁽¹²ᵉ⁾
      (A22⁽¹²ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00) .liftr.1 (refl a00)))
           (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10) (refl A11 .liftr.1 a11)
            .liftr.1 a12)
           (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .liftr.1 a20)
           (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00) .trr.1 (refl a00))
                (refl A11 .liftr.1 a11)
            .liftr.1 a21)
       .liftr.1 a22)
      (f02⁽¹ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00) .liftr.1 (refl a00))))
      (f12⁽¹ᵉ⁾
         (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10) (refl A11 .liftr.1 a11) .liftr.1 a12))
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00))
                (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr.1 a10))
            .liftr.1 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .liftr.1 a20))
           (f02⁽¹ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00)))
           (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr.1 a10)))
       .trl.1
         (refl f21
            (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00))
                 (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr.1 a10))
             .trr.1 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .liftr.1 a20))))
      (refl f21
         (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00) .trr.1 (refl a00))
              (refl A11 .liftr.1 a11)
          .liftr.1 a21))
    .trl.1
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                (sym
                   (A12⁽ᵉ¹⁾
                        (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                             (refl A11 .liftr.1 a11)
                         .trr.1 a12) (A12 .liftr.1 (refl A10 .trr.1 a10))
                    .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                 .liftr.1
                   (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .trr.1 a20))
                (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                     (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                               (refl A11 .liftr.1 a11)
                           .trr.1 a12) (A12 .liftr.1 (refl A10 .trr.1 a10))
                      .trr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                 .liftr.1
                   (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00) .trr.1 (refl a00))
                        (refl A11 .liftr.1 a11)
                    .trr.1 a21))
            .liftr.1
              (A22⁽¹²ᵉ⁾
                   (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00) .liftr.1 (refl a00)))
                   (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10) (refl A11 .liftr.1 a11)
                    .liftr.1 a12)
                   (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .liftr.1 a20)
                   (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00) .trr.1 (refl a00))
                        (refl A11 .liftr.1 a11)
                    .liftr.1 a21)
               .trr.1 a22)) (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
           (f12⁽¹ᵉ⁾
              (sym
                 (A12⁽ᵉ¹⁾
                      (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10) (refl A11 .liftr.1 a11)
                       .trr.1 a12) (A12 .liftr.1 (refl A10 .trr.1 a10))
                  .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))))
           (B22⁽¹²ᵉ⁾
                (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                     (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                 .liftr.1
                   (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                    .liftr.1
                      (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .trr.1 a20)))
                (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
                (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
            .trl.1
              (refl f21
                 (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                      (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                  .trr.1
                    (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                     .liftr.1
                       (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .trr.1 a20)))))
           (refl f21
              (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                   (A12⁽ᵉ¹⁾
                        (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                             (refl A11 .liftr.1 a11)
                         .trr.1 a12) (A12 .liftr.1 (refl A10 .trr.1 a10))
                    .trr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
               .liftr.1
                 (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00) .trr.1 (refl a00))
                      (refl A11 .liftr.1 a11)
                  .trr.1 a21)))
       .trl.1
         (B22⁽¹²ᵉ⁾
              (sym
                 (A22⁽ᵉ¹⁾ (sym (refl A02 .liftr.1 (refl a00)))
                      (sym (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                      (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                           (sym
                              (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                        (refl A11 .liftr.1 a11)
                                    .trr.1 a12)
                                   (A12 .liftr.1 (refl A10 .trr.1 a10))
                               .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                           (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                            .liftr.1
                              (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10)
                               .trr.1 a20))
                           (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                                (A12⁽ᵉ¹⁾
                                     (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                          (refl A11 .liftr.1 a11)
                                      .trr.1 a12)
                                     (A12 .liftr.1 (refl A10 .trr.1 a10))
                                 .trr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                            .liftr.1
                              (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00)
                                    .trr.1 (refl a00)) (refl A11 .liftr.1 a11)
                               .trr.1 a21))
                       .trr.1
                         (A22⁽¹²ᵉ⁾
                              (sym
                                 (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00)
                                  .liftr.1 (refl a00)))
                              (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                   (refl A11 .liftr.1 a11)
                               .liftr.1 a12)
                              (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10)
                               .liftr.1 a20)
                              (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00)
                                    .trr.1 (refl a00)) (refl A11 .liftr.1 a11)
                               .liftr.1 a21)
                          .trr.1 a22))
                      (A22 (A02 .liftr.1 a00)
                           (A12 .liftr.1 (refl A10 .trr.1 a10))
                       .liftr.1
                         (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                          .trr.1
                            (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10)
                             .trr.1 a20)))
                  .liftr.1
                    (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                     .trr.1
                       (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                        .trr.1 (refl a20)))))
              (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
              (f12⁽¹ᵉ⁾ (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
              (B22⁽¹²ᵉ⁾
                   (A22⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                        (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                    .liftr.1
                      (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                       .trr.1
                         (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                          .trr.1 (refl a20))))
                   (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
                   (f12⁽¹ᵉ⁾ (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
               .trl.1
                 (refl f21
                    (A22⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                         (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                     .trr.1
                       (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                        .trr.1
                          (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                           .trr.1 (refl a20))))))
              (refl f21
                 (A22⁽ᵉ¹⁾ (sym (refl A02 .liftr.1 (refl a00)))
                      (sym (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                      (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                           (sym
                              (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                        (refl A11 .liftr.1 a11)
                                    .trr.1 a12)
                                   (A12 .liftr.1 (refl A10 .trr.1 a10))
                               .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                           (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                            .liftr.1
                              (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10)
                               .trr.1 a20))
                           (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                                (A12⁽ᵉ¹⁾
                                     (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                          (refl A11 .liftr.1 a11)
                                      .trr.1 a12)
                                     (A12 .liftr.1 (refl A10 .trr.1 a10))
                                 .trr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                            .liftr.1
                              (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00)
                                    .trr.1 (refl a00)) (refl A11 .liftr.1 a11)
                               .trr.1 a21))
                       .trr.1
                         (A22⁽¹²ᵉ⁾
                              (sym
                                 (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00)
                                  .liftr.1 (refl a00)))
                              (A12⁽¹ᵉ⁾ (refl A10 .liftr.1 a10)
                                   (refl A11 .liftr.1 a11)
                               .liftr.1 a12)
                              (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10)
                               .liftr.1 a20)
                              (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 .liftr.1 a00)
                                    .trr.1 (refl a00)) (refl A11 .liftr.1 a11)
                               .liftr.1 a21)
                          .trr.1 a22))
                      (A22 (A02 .liftr.1 a00)
                           (A12 .liftr.1 (refl A10 .trr.1 a10))
                       .liftr.1
                         (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                          .trr.1
                            (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10)
                             .trr.1 a20)))
                  .trr.1
                    (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                     .trr.1
                       (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                        .trr.1 (refl a20)))))
          .trl.1
            (B22
                 (A22 (A02 .liftr.1 a00) (A12 .liftr.1 (refl A10 .trr.1 a10))
                  .liftr.1
                    (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                     .trr.1
                       (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .trr.1 a20)))
                 (f02 (A02 .liftr.1 a00))
                 (f12 (A12 .liftr.1 (refl A10 .trr.1 a10)))
             .liftl.1
               (f21
                  (A22 (A02 .liftr.1 a00) (A12 .liftr.1 (refl A10 .trr.1 a10))
                   .trr.1
                     (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                      .trr.1
                        (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr.1 a10) .trr.1 a20)))))))
    : B22 a22 (f02 a02) (f12 a12)
        (B22 (A22 (A02 .liftr.1 a00) (A12 .liftr.1 a10) .liftr.1 a20)
             (f02 (A02 .liftr.1 a00)) (f12 (A12 .liftr.1 a10))
         .trl.1 (f21 (A22 (A02 .liftr.1 a00) (A12 .liftr.1 a10) .trr.1 a20)))
        (f21 a21)
  
