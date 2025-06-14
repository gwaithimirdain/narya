  $ narya -v sym.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a00 assumed
  
   ￫ info[I0001]
   ￮ axiom a01 assumed
  
   ￫ info[I0001]
   ￮ axiom a02 assumed
  
   ￫ info[I0001]
   ￮ axiom a10 assumed
  
   ￫ info[I0001]
   ￮ axiom a11 assumed
  
   ￫ info[I0001]
   ￮ axiom a12 assumed
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0001]
   ￮ axiom a22 assumed
  
  sym a22
    : A⁽ᵉᵉ⁾ a20 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a02 a12 a20 a21
  
   ￫ info[I0000]
   ￮ constant sym_involution defined
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
   ￫ info[I0000]
   ￮ constant ap_sym defined
  

  $ narya sym.ny -e "echo sym a00"
  sym a22
    : A⁽ᵉᵉ⁾ a20 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a02 a12 a20 a21
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo sym a00
     ^ argument of degeneracy 'sym' must have dimension at least ee
  
  [1]

  $ narya sym.ny -e "echo sym a02"
  sym a22
    : A⁽ᵉᵉ⁾ a20 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a02 a12 a20 a21
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo sym a02
     ^ argument of degeneracy 'sym' must have dimension at least ee
  
  [1]

  $ narya -v symsym.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a000 assumed
  
   ￫ info[I0001]
   ￮ axiom a001 assumed
  
   ￫ info[I0001]
   ￮ axiom a002 assumed
  
   ￫ info[I0001]
   ￮ axiom a010 assumed
  
   ￫ info[I0001]
   ￮ axiom a011 assumed
  
   ￫ info[I0001]
   ￮ axiom a012 assumed
  
   ￫ info[I0001]
   ￮ axiom a020 assumed
  
   ￫ info[I0001]
   ￮ axiom a021 assumed
  
   ￫ info[I0001]
   ￮ axiom a022 assumed
  
   ￫ info[I0001]
   ￮ axiom a100 assumed
  
   ￫ info[I0001]
   ￮ axiom a101 assumed
  
   ￫ info[I0001]
   ￮ axiom a102 assumed
  
   ￫ info[I0001]
   ￮ axiom a110 assumed
  
   ￫ info[I0001]
   ￮ axiom a111 assumed
  
   ￫ info[I0001]
   ￮ axiom a112 assumed
  
   ￫ info[I0001]
   ￮ axiom a120 assumed
  
   ￫ info[I0001]
   ￮ axiom a121 assumed
  
   ￫ info[I0001]
   ￮ axiom a122 assumed
  
   ￫ info[I0001]
   ￮ axiom a200 assumed
  
   ￫ info[I0001]
   ￮ axiom a201 assumed
  
   ￫ info[I0001]
   ￮ axiom a202 assumed
  
   ￫ info[I0001]
   ￮ axiom a210 assumed
  
   ￫ info[I0001]
   ￮ axiom a211 assumed
  
   ￫ info[I0001]
   ￮ axiom a212 assumed
  
   ￫ info[I0001]
   ￮ axiom a220 assumed
  
   ￫ info[I0001]
   ￮ axiom a221 assumed
  
   ￫ info[I0001]
   ￮ axiom a222 assumed
  
  a222
    : A⁽ᵉᵉᵉ⁾ a022 a122 a202 a212 a220 a221
  
  a222
    : A⁽ᵉᵉᵉ⁾ a022 a122 a202 a212 a220 a221
  
  sym a222
    : A⁽ᵉᵉᵉ⁾ (sym a022) (sym a122) a220 a221 a202 a212
  
  a222⁽¹³²⁾
    : A⁽ᵉᵉᵉ⁾ (sym a022) (sym a122) a220 a221 a202 a212
  
   ￫ info[I0000]
   ￮ constant sym2 defined
  
  a222⁽²¹³⁾
    : A⁽ᵉᵉᵉ⁾ a202 a212 a022 a122 (sym a220) (sym a221)
  
  a222⁽²¹³⁾
    : A⁽ᵉᵉᵉ⁾ a202 a212 a022 a122 (sym a220) (sym a221)
  
  a222⁽³¹²⁾
    : A⁽ᵉᵉᵉ⁾ a220 a221 (sym a022) (sym a122) (sym a202) (sym a212)
  
  a222⁽³¹²⁾
    : A⁽ᵉᵉᵉ⁾ a220 a221 (sym a022) (sym a122) (sym a202) (sym a212)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
        (sym a122)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
        (sym a122)
  
  a222⁽²³¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a202) (sym a212) (sym a220) (sym a221) a022 a122
  
  a222⁽²³¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a202) (sym a212) (sym a220) (sym a221) a022 a122
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
        (sym a122)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
        (sym a122)
  
   ￫ info[I0000]
   ￮ constant braid defined
  
   ￫ info[I0000]
   ￮ constant braid2 defined
  

  $ narya -v checksym.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom a00 assumed
  
   ￫ info[I0001]
   ￮ axiom a01 assumed
  
   ￫ info[I0001]
   ￮ axiom a02 assumed
  
   ￫ info[I0001]
   ￮ axiom a10 assumed
  
   ￫ info[I0001]
   ￮ axiom a11 assumed
  
   ￫ info[I0001]
   ￮ axiom a12 assumed
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0001]
   ￮ axiom a22 assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0001]
   ￮ axiom b00 assumed
  
   ￫ info[I0001]
   ￮ axiom b01 assumed
  
   ￫ info[I0001]
   ￮ axiom b02 assumed
  
   ￫ info[I0001]
   ￮ axiom b10 assumed
  
   ￫ info[I0001]
   ￮ axiom b11 assumed
  
   ￫ info[I0001]
   ￮ axiom b12 assumed
  
   ￫ info[I0001]
   ￮ axiom b20 assumed
  
   ￫ info[I0001]
   ￮ axiom b21 assumed
  
   ￫ info[I0001]
   ￮ axiom b22 assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant ab22 defined
  
   ￫ info[I0000]
   ￮ constant sym_ab22 defined
  
   ￫ info[I0000]
   ￮ constant sym_ab22' defined
  

  $ narya -v symfield.ny
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0001]
   ￮ axiom a00 assumed
  
   ￫ info[I0001]
   ￮ axiom a01 assumed
  
   ￫ info[I0001]
   ￮ axiom a02 assumed
  
   ￫ info[I0001]
   ￮ axiom a10 assumed
  
   ￫ info[I0001]
   ￮ axiom a11 assumed
  
   ￫ info[I0001]
   ￮ axiom a12 assumed
  
   ￫ info[I0001]
   ￮ axiom a20 assumed
  
   ￫ info[I0001]
   ￮ axiom a21 assumed
  
   ￫ info[I0001]
   ￮ axiom a22 assumed
  
  sym a22 .unwrap
    : B⁽ᵉᵉ⁾ (a20 .unwrap) (a21 .unwrap) (a02 .unwrap) (a12 .unwrap)
  
  sym a22 .unwrap
    : B⁽ᵉᵉ⁾ (a20 .unwrap) (a21 .unwrap) (a02 .unwrap) (a12 .unwrap)
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  
