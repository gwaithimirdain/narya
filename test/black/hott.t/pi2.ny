{` Transport and lifting compute on 2-dimensional Π-types `}

axiom A00 : Type

axiom A01 : Type

axiom A02 : Id Type A00 A01

axiom A10 : Type

axiom A11 : Type

axiom A12 : Id Type A10 A11

axiom A20 : Id Type A00 A10

axiom A21 : Id Type A01 A11

axiom A22 : Type⁽ᵉᵉ⁾ A02 A12 A20 A21

axiom B00 : A00 → Type

axiom B01 : A01 → Type

axiom B02 : Id ((X ↦ X → Type) : Type → Type) (A02) B00 B01

axiom B10 : A10 → Type

axiom B11 : A11 → Type

axiom B12 : Id ((X ↦ X → Type) : Type → Type) (A12) B10 B11

axiom B20 : Id ((X ↦ X → Type) : Type → Type) (A20) B00 B10

axiom B21 : Id ((X ↦ X → Type) : Type → Type) (A21) B01 B11

axiom B22 : ((X ↦ X → Type) : Type → Type)⁽ᵉᵉ⁾ (A22) B02 B12 B20 B21

axiom f00 : (x00 : A00) → B00 x00

axiom f01 : (x01 : A01) → B01 x01

axiom f02
  : Id ((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type)) A02 B02
      f00 f01

axiom a10 : A10

axiom a11 : A11

axiom a12 : A12 a10 a11

axiom f10 : (x10 : A10) → B10 x10

axiom f11 : (x11 : A11) → B11 x11

axiom f12
  : Id ((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type)) A12 B12
      f10 f11

axiom f20
  : Id ((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type)) A20 B20
      f00 f10

axiom f21
  : Id ((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type)) A21 B21
      f01 f11

axiom a01 : A01

axiom a21 : A21 a01 a11

{` 1-box-filling acting on 1-dimensional functions `}
echo ((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type))⁽ᵉᵉ⁾ A22
         B22 f02 f12
  .trr f20 a21

{` This is what it produces, which does indeed have the right type and is equal to it! `}
echo B22 (A22 (A02 .liftl a01) (A12 .liftl a11) .liftl a21)
         (f02 (A02 .liftl a01)) (f12 (A12 .liftl a11))
  .trr (f20 (A22 (A02 .liftl a01) (A12 .liftl a11) .trl a21))

def Πtrr
  : Id (B21 a21 (f01 a01) (f11 a11))
      (((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type))⁽ᵉᵉ⁾ A22
           B22 f02 f12
       .trr.1 f20 a21)
      (B22 (A22 (A02 .liftl a01) (A12 .liftl a11) .liftl a21)
           (f02 (A02 .liftl a01)) (f12 (A12 .liftl a11))
       .trr (f20 (A22 (A02 .liftl a01) (A12 .liftl a11) .trl a21)))
  ≔ refl _

{` And in the other direction `}

axiom a00 : A00

axiom a20 : A20 a00 a10

echo ((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type))⁽ᵉᵉ⁾ A22
         B22 f02 f12
  .trl f21 a20

echo B22 (A22 (A02 .liftr a00) (A12 .liftr a10) .liftr a20)
         (f02 (A02 .liftr a00)) (f12 (A12 .liftr a10))
  .trl (f21 (A22 (A02 .liftr a00) (A12 .liftr a10) .trr a20))

def Πtrl
  : Id (B20 a20 (f00 a00) (f10 a10))
      (((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type))⁽ᵉᵉ⁾ A22
           B22 f02 f12
       .trl.1 f21 a20)
      (B22 (A22 (A02 .liftr a00) (A12 .liftr a10) .liftr a20)
           (f02 (A02 .liftr a00)) (f12 (A12 .liftr a10))
       .trl (f21 (A22 (A02 .liftr a00) (A12 .liftr a10) .trr a20)))
  ≔ refl _

{` Now lifting `}
axiom a02 : A02 a00 a01

axiom a22 : A22 a02 a12 a20 a21

echo ((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type))⁽ᵉᵉ⁾ A22
         B22 f02 f12
  .liftr f20 a22

def Πliftr
  : Id
      (B22 a22 (f02 a02) (f12 a12) (f20 a20)
         (B22 (A22 (A02 .liftl a01) (A12 .liftl a11) .liftl a21)
              (f02 (A02 .liftl a01)) (f12 (A12 .liftl a11))
          .trr (f20 (A22 (A02 .liftl a01) (A12 .liftl a11) .trl a21))))
      (((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type))⁽ᵉᵉ⁾ A22
           B22 f02 f12
       .liftr f20 a22)
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .liftl (refl a01)))
                (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                 .liftr a12)
                (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                     (refl A10 .liftr a10)
                 .liftr a20)
                (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .liftr a21)
            .liftr a22)
           (f02⁽¹ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .liftl (refl a01))))
           (f12⁽¹ᵉ⁾
              (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
               .liftr a12))
           (refl f20
              (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                   (refl A10 .liftr a10)
               .liftr a20))
           (B22⁽¹²ᵉ⁾
                (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01))
                     (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr a11))
                 .liftl.1
                   (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .liftr a21))
                (f02⁽¹ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01)))
                (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr a11)))
            .trr.1
              (refl f20
                 (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftl.1 (refl a01))
                      (A12⁽¹ᵉ⁾ .liftl.1 (refl A11 .liftr a11))
                  .trl.1
                    (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .liftr a21))))
       .trl
         (B22⁽¹²ᵉ⁾
              (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                   (sym
                      (A12⁽ᵉ¹⁾
                           (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                (refl A11 .liftr a11)
                            .trr a12) (A12 .liftl (refl A11 .trr a11))
                       .liftl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                   (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                        (A12⁽ᵉ¹⁾
                             (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                  (refl A11 .liftr a11)
                              .trr a12) (A12 .liftl (refl A11 .trr a11))
                         .trl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                    .liftr
                      (A20⁽¹ᵉ⁾
                           (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                           (refl A10 .liftr a10)
                       .trr a20))
                   (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                    .liftr
                      (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21))
               .liftr
                 (A22⁽¹²ᵉ⁾
                      (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .liftl (refl a01)))
                      (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                       .liftr a12)
                      (A20⁽¹ᵉ⁾
                           (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                           (refl A10 .liftr a10)
                       .liftr a20)
                      (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .liftr a21)
                  .trr a22)) (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
              (f12⁽¹ᵉ⁾
                 (sym
                    (A12⁽ᵉ¹⁾
                         (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                              (refl A11 .liftr a11)
                          .trr a12) (A12 .liftl (refl A11 .trr a11))
                     .liftl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))))
              (refl f20
                 (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                      (A12⁽ᵉ¹⁾
                           (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                (refl A11 .liftr a11)
                            .trr a12) (A12 .liftl (refl A11 .trr a11))
                       .trl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                  .liftr
                    (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01) .trl (refl a01))
                         (refl A10 .liftr a10)
                     .trr a20)))
              (B22⁽¹²ᵉ⁾
                   (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                        (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                    .liftl.1
                      (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                       .liftr
                         (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11) .trr a21)))
                   (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
                   (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
               .trr.1
                 (refl f20
                    (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                         (A12⁽¹ᵉ⁾ .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                     .trl.1
                       (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                        .liftr
                          (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                           .trr a21)))))
          .trl
            (B22⁽¹²ᵉ⁾
                 (sym
                    (A22⁽ᵉ¹⁾ (sym (refl A02 .liftl.1 (refl a01)))
                         (sym
                            (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                         (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                              (sym
                                 (A12⁽ᵉ¹⁾
                                      (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                           (refl A11 .liftr a11)
                                       .trr a12)
                                      (A12 .liftl (refl A11 .trr a11))
                                  .liftl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                              (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                                   (A12⁽ᵉ¹⁾
                                        (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                             (refl A11 .liftr a11)
                                         .trr a12)
                                        (A12 .liftl (refl A11 .trr a11))
                                    .trl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                               .liftr
                                 (A20⁽¹ᵉ⁾
                                      (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                       .trl (refl a01))
                                      (refl A10 .liftr a10)
                                  .trr a20))
                              (A21⁽¹ᵉ⁾ (refl a01)
                                   (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                               .liftr
                                 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                                  .trr a21))
                          .trr
                            (A22⁽¹²ᵉ⁾
                                 (sym
                                    (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                     .liftl (refl a01)))
                                 (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                      (refl A11 .liftr a11)
                                  .liftr a12)
                                 (A20⁽¹ᵉ⁾
                                      (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                       .trl (refl a01))
                                      (refl A10 .liftr a10)
                                  .liftr a20)
                                 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                                  .liftr a21)
                             .trr a22))
                         (A22 (A02 .liftl a01)
                              (A12 .liftl (refl A11 .trr a11))
                          .liftl
                            (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                             .trr
                               (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                                .trr a21)))
                     .liftl
                       (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                        .trr.1
                          (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                           .trr.1 (refl a21)))))
                 (f02⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01)))
                 (f12⁽¹ᵉ⁾ (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                 (refl f20
                    (A22⁽ᵉ¹⁾ (sym (refl A02 .liftl.1 (refl a01)))
                         (sym
                            (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                         (A22⁽¹²ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                              (sym
                                 (A12⁽ᵉ¹⁾
                                      (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                           (refl A11 .liftr a11)
                                       .trr a12)
                                      (A12 .liftl (refl A11 .trr a11))
                                  .liftl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                              (A20⁽¹ᵉ⁾ (refl A02 .trl.1 (refl a01))
                                   (A12⁽ᵉ¹⁾
                                        (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                             (refl A11 .liftr a11)
                                         .trr a12)
                                        (A12 .liftl (refl A11 .trr a11))
                                    .trl (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                               .liftr
                                 (A20⁽¹ᵉ⁾
                                      (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                       .trl (refl a01))
                                      (refl A10 .liftr a10)
                                  .trr a20))
                              (A21⁽¹ᵉ⁾ (refl a01)
                                   (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                               .liftr
                                 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                                  .trr a21))
                          .trr
                            (A22⁽¹²ᵉ⁾
                                 (sym
                                    (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                     .liftl (refl a01)))
                                 (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                      (refl A11 .liftr a11)
                                  .liftr a12)
                                 (A20⁽¹ᵉ⁾
                                      (A02⁽ᵉ¹⁾ a02 (A02 .liftl a01)
                                       .trl (refl a01))
                                      (refl A10 .liftr a10)
                                  .liftr a20)
                                 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                                  .liftr a21)
                             .trr a22))
                         (A22 (A02 .liftl a01)
                              (A12 .liftl (refl A11 .trr a11))
                          .liftl
                            (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                             .trr
                               (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                                .trr a21)))
                     .trl
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
                      (f12⁽¹ᵉ⁾
                         (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))))
                  .trr.1
                    (refl f20
                       (A22⁽¹ᵉ⁾ (refl A02 .liftl.1 (refl a01))
                            (refl A12 .liftl.1 (A11⁽ᵉᵉ⁾ .trr.1 (refl a11)))
                        .trl.1
                          (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ .trr.1 a11⁽ᵉᵉ⁾)
                           .trr.1
                             (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾
                                  (A11⁽ᵉᵉ⁾ .liftr.1 (refl a11))
                              .trr.1 (refl a21))))))
             .trl
               (B22
                    (A22 (A02 .liftl a01) (A12 .liftl (refl A11 .trr a11))
                     .liftl
                       (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                        .trr
                          (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                           .trr a21))) (f02 (A02 .liftl a01))
                    (f12 (A12 .liftl (refl A11 .trr a11)))
                .liftr
                  (f20
                     (A22 (A02 .liftl a01) (A12 .liftl (refl A11 .trr a11))
                      .trl
                        (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ .trr.1 (refl a11))
                         .trr
                           (A21⁽¹ᵉ⁾ (refl a01) (refl A11 .liftr a11)
                            .trr a21))))))))
  ≔ refl _

echo ((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type))⁽ᵉᵉ⁾ A22
         B22 f02 f12
  .liftl f21 a22

def Πliftl
  : Id
      (B22 a22 (f02 a02) (f12 a12)
         (B22 (A22 (A02 .liftr a00) (A12 .liftr a10) .liftr a20)
              (f02 (A02 .liftr a00)) (f12 (A12 .liftr a10))
          .trl (f21 (A22 (A02 .liftr a00) (A12 .liftr a10) .trr a20)))
         (f21 a21))
      (((X Y ↦ (x : X) → Y x) : ((X : Type) (Y : X → Type) → Type))⁽ᵉᵉ⁾ A22
           B22 f02 f12
       .liftl f21 a22)
      (B22⁽¹²ᵉ⁾
           (A22⁽¹²ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .liftr (refl a00)))
                (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                 .liftr a12)
                (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .liftr a20)
                (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                     (refl A11 .liftr a11)
                 .liftr a21)
            .liftr a22)
           (f02⁽¹ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .liftr (refl a00))))
           (f12⁽¹ᵉ⁾
              (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
               .liftr a12))
           (B22⁽¹²ᵉ⁾
                (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00))
                     (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr a10))
                 .liftr.1
                   (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .liftr a20))
                (f02⁽¹ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00)))
                (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr a10)))
            .trl.1
              (refl f21
                 (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ .liftr.1 (refl a00))
                      (A12⁽¹ᵉ⁾ .liftr.1 (refl A10 .liftr a10))
                  .trr.1
                    (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .liftr a20))))
           (refl f21
              (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                   (refl A11 .liftr a11)
               .liftr a21))
       .trl
         (B22⁽¹²ᵉ⁾
              (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                   (sym
                      (A12⁽ᵉ¹⁾
                           (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                (refl A11 .liftr a11)
                            .trr a12) (A12 .liftr (refl A10 .trr a10))
                       .liftr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                   (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                    .liftr
                      (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20))
                   (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                        (A12⁽ᵉ¹⁾
                             (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                  (refl A11 .liftr a11)
                              .trr a12) (A12 .liftr (refl A10 .trr a10))
                         .trr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                    .liftr
                      (A21⁽¹ᵉ⁾
                           (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                           (refl A11 .liftr a11)
                       .trr a21))
               .liftr
                 (A22⁽¹²ᵉ⁾
                      (sym (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .liftr (refl a00)))
                      (A12⁽¹ᵉ⁾ (refl A10 .liftr a10) (refl A11 .liftr a11)
                       .liftr a12)
                      (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .liftr a20)
                      (A21⁽¹ᵉ⁾
                           (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                           (refl A11 .liftr a11)
                       .liftr a21)
                  .trr a22)) (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
              (f12⁽¹ᵉ⁾
                 (sym
                    (A12⁽ᵉ¹⁾
                         (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                              (refl A11 .liftr a11)
                          .trr a12) (A12 .liftr (refl A10 .trr a10))
                     .liftr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))))
              (B22⁽¹²ᵉ⁾
                   (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                        (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                    .liftr.1
                      (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                       .liftr
                         (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10) .trr a20)))
                   (f02⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00)))
                   (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
               .trl.1
                 (refl f21
                    (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                         (A12⁽¹ᵉ⁾ .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                     .trr.1
                       (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                        .liftr
                          (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                           .trr a20)))))
              (refl f21
                 (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                      (A12⁽ᵉ¹⁾
                           (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                (refl A11 .liftr a11)
                            .trr a12) (A12 .liftr (refl A10 .trr a10))
                       .trr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                  .liftr
                    (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00) .trr (refl a00))
                         (refl A11 .liftr a11)
                     .trr a21)))
          .trl
            (B22⁽¹²ᵉ⁾
                 (sym
                    (A22⁽ᵉ¹⁾ (sym (refl A02 .liftr.1 (refl a00)))
                         (sym
                            (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                         (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                              (sym
                                 (A12⁽ᵉ¹⁾
                                      (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                           (refl A11 .liftr a11)
                                       .trr a12)
                                      (A12 .liftr (refl A10 .trr a10))
                                  .liftr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                              (A20⁽¹ᵉ⁾ (refl a00)
                                   (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                               .liftr
                                 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                                  .trr a20))
                              (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                                   (A12⁽ᵉ¹⁾
                                        (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                             (refl A11 .liftr a11)
                                         .trr a12)
                                        (A12 .liftr (refl A10 .trr a10))
                                    .trr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                               .liftr
                                 (A21⁽¹ᵉ⁾
                                      (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                       .trr (refl a00))
                                      (refl A11 .liftr a11)
                                  .trr a21))
                          .trr
                            (A22⁽¹²ᵉ⁾
                                 (sym
                                    (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                     .liftr (refl a00)))
                                 (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                      (refl A11 .liftr a11)
                                  .liftr a12)
                                 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                                  .liftr a20)
                                 (A21⁽¹ᵉ⁾
                                      (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                       .trr (refl a00))
                                      (refl A11 .liftr a11)
                                  .liftr a21)
                             .trr a22))
                         (A22 (A02 .liftr a00)
                              (A12 .liftr (refl A10 .trr a10))
                          .liftr
                            (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                             .trr
                               (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                                .trr a20)))
                     .liftr
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
                      (f12⁽¹ᵉ⁾
                         (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                  .trl.1
                    (refl f21
                       (A22⁽¹ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                            (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                        .trr.1
                          (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                           .trr.1
                             (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾
                                  (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                              .trr.1 (refl a20))))))
                 (refl f21
                    (A22⁽ᵉ¹⁾ (sym (refl A02 .liftr.1 (refl a00)))
                         (sym
                            (refl A12 .liftr.1 (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                         (A22⁽¹²ᵉ⁾ (refl A02 .liftr.1 (refl a00))
                              (sym
                                 (A12⁽ᵉ¹⁾
                                      (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                           (refl A11 .liftr a11)
                                       .trr a12)
                                      (A12 .liftr (refl A10 .trr a10))
                                  .liftr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))))
                              (A20⁽¹ᵉ⁾ (refl a00)
                                   (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                               .liftr
                                 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                                  .trr a20))
                              (A21⁽¹ᵉ⁾ (refl A02 .trr.1 (refl a00))
                                   (A12⁽ᵉ¹⁾
                                        (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                             (refl A11 .liftr a11)
                                         .trr a12)
                                        (A12 .liftr (refl A10 .trr a10))
                                    .trr (A10⁽ᵉᵉ⁾ .trr.1 (refl a10)))
                               .liftr
                                 (A21⁽¹ᵉ⁾
                                      (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                       .trr (refl a00))
                                      (refl A11 .liftr a11)
                                  .trr a21))
                          .trr
                            (A22⁽¹²ᵉ⁾
                                 (sym
                                    (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                     .liftr (refl a00)))
                                 (A12⁽¹ᵉ⁾ (refl A10 .liftr a10)
                                      (refl A11 .liftr a11)
                                  .liftr a12)
                                 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                                  .liftr a20)
                                 (A21⁽¹ᵉ⁾
                                      (A02⁽ᵉ¹⁾ a02 (A02 .liftr a00)
                                       .trr (refl a00))
                                      (refl A11 .liftr a11)
                                  .liftr a21)
                             .trr a22))
                         (A22 (A02 .liftr a00)
                              (A12 .liftr (refl A10 .trr a10))
                          .liftr
                            (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                             .trr
                               (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                                .trr a20)))
                     .trr
                       (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ .trr.1 a10⁽ᵉᵉ⁾)
                        .trr.1
                          (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉ⁾ .liftr.1 (refl a10))
                           .trr.1 (refl a20)))))
             .trl
               (B22
                    (A22 (A02 .liftr a00) (A12 .liftr (refl A10 .trr a10))
                     .liftr
                       (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                        .trr
                          (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                           .trr a20))) (f02 (A02 .liftr a00))
                    (f12 (A12 .liftr (refl A10 .trr a10)))
                .liftl
                  (f21
                     (A22 (A02 .liftr a00) (A12 .liftr (refl A10 .trr a10))
                      .trr
                        (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ .trr.1 (refl a10))
                         .trr
                           (A20⁽¹ᵉ⁾ (refl a00) (refl A10 .liftr a10)
                            .trr a20))))))))
  ≔ refl _
