  $ narya -v hct.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant √A defined
  
   ￫ info[I0001]
   ￮ axiom s0 assumed
  
   ￫ info[I0001]
   ￮ axiom s1 assumed
  
   ￫ info[I0001]
   ￮ axiom s2 assumed
  
  s2 .root.1
    : A
  
   ￫ info[I0001]
   ￮ axiom s00 assumed
  
   ￫ info[I0001]
   ￮ axiom s01 assumed
  
   ￫ info[I0001]
   ￮ axiom s10 assumed
  
   ￫ info[I0001]
   ￮ axiom s11 assumed
  
   ￫ info[I0001]
   ￮ axiom s02 assumed
  
   ￫ info[I0001]
   ￮ axiom s12 assumed
  
   ￫ info[I0001]
   ￮ axiom s20 assumed
  
   ￫ info[I0001]
   ￮ axiom s21 assumed
  
   ￫ info[I0001]
   ￮ axiom s22 assumed
  
  sym s22 .root.2
    : refl A (s02 .root.1) (s12 .root.1)
  
  s22 .root.2
    : refl A (s20 .root.1) (s21 .root.1)
  

  $ narya -v 2dct.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant √√A defined
  
   ￫ info[I0001]
   ￮ axiom s000 assumed
  
   ￫ info[I0001]
   ￮ axiom s001 assumed
  
   ￫ info[I0001]
   ￮ axiom s002 assumed
  
   ￫ info[I0001]
   ￮ axiom s010 assumed
  
   ￫ info[I0001]
   ￮ axiom s011 assumed
  
   ￫ info[I0001]
   ￮ axiom s012 assumed
  
   ￫ info[I0001]
   ￮ axiom s020 assumed
  
   ￫ info[I0001]
   ￮ axiom s021 assumed
  
   ￫ info[I0001]
   ￮ axiom s022 assumed
  
   ￫ info[I0001]
   ￮ axiom s100 assumed
  
   ￫ info[I0001]
   ￮ axiom s101 assumed
  
   ￫ info[I0001]
   ￮ axiom s102 assumed
  
   ￫ info[I0001]
   ￮ axiom s110 assumed
  
   ￫ info[I0001]
   ￮ axiom s111 assumed
  
   ￫ info[I0001]
   ￮ axiom s112 assumed
  
   ￫ info[I0001]
   ￮ axiom s120 assumed
  
   ￫ info[I0001]
   ￮ axiom s121 assumed
  
   ￫ info[I0001]
   ￮ axiom s122 assumed
  
   ￫ info[I0001]
   ￮ axiom s200 assumed
  
   ￫ info[I0001]
   ￮ axiom s201 assumed
  
   ￫ info[I0001]
   ￮ axiom s202 assumed
  
   ￫ info[I0001]
   ￮ axiom s210 assumed
  
   ￫ info[I0001]
   ￮ axiom s211 assumed
  
   ￫ info[I0001]
   ￮ axiom s212 assumed
  
   ￫ info[I0001]
   ￮ axiom s220 assumed
  
   ￫ info[I0001]
   ￮ axiom s221 assumed
  
   ￫ info[I0001]
   ￮ axiom s222 assumed
  
  s222⁽³¹²⁾ .rroot.23
    : refl A (s022 .rroot.12) (s122 .rroot.12)
  
  s222⁽²¹³⁾ .rroot.23
    : refl A (s202 .rroot.12) (s212 .rroot.12)
  
  s222 .rroot.23
    : refl A (s220 .rroot.12) (s221 .rroot.12)
  
  s222⁽³²¹⁾ .rroot.23
    : refl A (sym s022 .rroot.12) (sym s122 .rroot.12)
  
  s222⁽¹³²⁾ .rroot.23
    : refl A (sym s220 .rroot.12) (sym s221 .rroot.12)
  
  s222⁽²³¹⁾ .rroot.23
    : refl A (sym s202 .rroot.12) (sym s212 .rroot.12)
  
