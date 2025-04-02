  $ narya -v constrs.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0000]
   ￮ constant twos defined
  
   ￫ info[I0002]
   ￮ notation twos.foo defined
  
   ￫ info[I0000]
   ￮ constant threes defined
  
   ￫ info[I0002]
   ￮ notation threes.foo defined
  
   ￫ info[I0001]
   ￮ axiom a assumed
  
   ￫ info[I0000]
   ￮ constant a2 defined
  
  a + a
    : twos
  
   ￫ info[I0000]
   ￮ constant a3 defined
  
  a * a * a
    : threes
  
  $ narya -v minus.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant ℕ.plus defined
  
   ￫ info[I0000]
   ￮ constant ℤ defined
  
   ￫ info[I0000]
   ￮ constant zero defined
  
   ￫ info[I0000]
   ￮ constant one defined
  
   ￫ info[I0000]
   ￮ constant two defined
  
   ￫ info[I0000]
   ￮ constant three defined
  
   ￫ info[I0000]
   ￮ constant minus_one defined
  
   ￫ info[I0000]
   ￮ constant minus_two defined
  
   ￫ info[I0000]
   ￮ constant minus_three defined
  
   ￫ info[I0000]
   ￮ constant ℤ.minus defined
  
   ￫ info[I0000]
   ￮ constant ℕ.sub defined
  
   ￫ info[I0000]
   ￮ constant ℤ.sub defined
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  4
    : ℤ
  
  negsuc. 3
    : ℤ
  
  0
    : ℤ
  
  0
    : ℤ
  
   ￫ info[I0002]
   ￮ notation sub defined
  
   ￫ info[I0002]
   ￮ notation minus defined
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  negsuc. 1
    : ℤ
  
  negsuc. 1
    : ℤ
  
  2
    : ℤ
  
  0
    : ℤ
  
  0
    : ℤ
  
   ￫ warning[E2209]
   ￮ replacing printing notation for ℤ.minus (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation minus' defined
  
  2
    : ℤ
  
   ￫ error[E0201]
   ￮ potential parsing ambiguity: One notation is a prefix of another: [minus] and [minus']
  
  [1]
