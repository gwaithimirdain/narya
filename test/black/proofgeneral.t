ProofGeneral interaction mode.  Each command is followed by a line containing
only a formfeed, as ProofGeneral sends it.  The output is piped through sed so
that the formfeeds (^L) and the escape characters of ANSI color codes (^[) are
visible.

  $ printf 'axiom A : Type\n\f\n' > input
  $ printf 'axiom a : A\n\f\n' >> input
  $ printf 'def id : A → A ≔ x ↦ x\n\f\n' >> input
  $ printf 'echo id a\n\f\n' >> input
  $ printf 'synth id\n\f\n' >> input
  $ printf 'about id\n\f\n' >> input
  $ printf 'def f : A → A ≔ ?\n\f\n' >> input
  $ printf 'echo in 0 id\n\f\n' >> input
  $ printf 'synth in 0 a\n\f\n' >> input
  $ printf 'show holes\n\f\n' >> input
  $ printf 'echo b\n\f\n' >> input
  $ printf 'echo (a\n\f\n' >> input
  $ narya -proofgeneral < input | sed 's/\x0c/^L/g; s/\x1b/^[/g'
  ^L[narya]^L
   ￫ ^[[32minfo[I0001]^[[m
   ￮ ^[[32maxiom A assumed^[[m
  
  ^L[goals]^L
  ^L[data]^L
  unparenthesized
  1
  ^L[reformat]^L
  axiom A : Type^L[narya]^L
   ￫ ^[[32minfo[I0001]^[[m
   ￮ ^[[32maxiom a assumed^[[m
  
  ^L[goals]^L
  ^L[data]^L
  unparenthesized
  2
  ^L[reformat]^L
  axiom a : A^L[narya]^L
   ￫ ^[[32minfo[I0000]^[[m
   ￮ ^[[32mconstant id defined^[[m
  
  ^L[goals]^L
  ^L[data]^L
  unparenthesized
  3
  ^L[reformat]^L
  def id : A → A ≔ x ↦ x^L[narya]^L
  a
    : A
  
  ^L[goals]^L
  ^L[data]^L
  unparenthesized
  3
  ^L[reformat]^L
  echo id a^L[narya]^L
  id
    : A → A
  
  ^L[goals]^L
  ^L[data]^L
  unparenthesized
  3
  ^L[reformat]^L
  synth id^L[narya]^L
  x ↦ x
    : A → A
  
  ^L[goals]^L
  ^L[data]^L
  unparenthesized
  3
  ^L[reformat]^L
  about id^L[narya]^L
   ￫ ^[[32minfo[I0000]^[[m
   ￮ ^[[32mconstant f defined, containing 1 hole^[[m
  
   ￫ ^[[33mwarning[W3000]^[[m
   ￮ ^[[33mthere is 1 open hole^[[m
  
  ^L[goals]^L
  hole ?0:
  
  ----------------------------------------------------------------------
  A → A
  
  ^L[data]^L
  unparenthesized
  4
  0 20 21
  ^L[reformat]^L
  def f : A → A ≔ ⁇0¿ʔ^L[narya]^L
  id
    : A → A
  
   ￫ ^[[33mwarning[W3000]^[[m
   ￮ ^[[33mthere is 1 open hole^[[m
  
  ^L[goals]^L
  hole ?0:
  
  ----------------------------------------------------------------------
  A → A
  
  ^L[data]^L
  unparenthesized
  4
  ^L[reformat]^L
  echo in 0 id^L[narya]^L
  a
    : A
  
   ￫ ^[[33mwarning[W3000]^[[m
   ￮ ^[[33mthere is 1 open hole^[[m
  
  ^L[goals]^L
  hole ?0:
  
  ----------------------------------------------------------------------
  A → A
  
  ^L[data]^L
  unparenthesized
  4
  ^L[reformat]^L
  synth in 0 a^L[narya]^L
   ￫ ^[[33mwarning[W3000]^[[m
   ￮ ^[[33mthere is 1 open hole^[[m
  
  ^L[goals]^L
  hole ?0:
  
  ----------------------------------------------------------------------
  A → A
  
  ^L[data]^L
  unparenthesized
  4
  ^L[reformat]^L
  ^L[narya]^L
   ￫ ^[[31merror[E0300]^[[m
   ^[[2m1 |^[[m echo ^[[4;31mb^[[m
     ^[[2m^^[[m ^[[31munbound variable: b^[[m
  
  ^L[errors]^L
  5 6
  ^L[narya]^L
   ￫ ^[[31merror[E0200]^[[m
   ^[[2m2 |^[[m ^[[4;31m‹EOF›^[[m
     ^[[2m^^[[m ^[[31mparse error: invalid syntax^[[m
  
  ^L[errors]^L
  8
  ^L[narya]^L
