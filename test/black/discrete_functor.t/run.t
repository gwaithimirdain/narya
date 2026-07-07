The -discrete-functor mode theory is like -functor, but its domain mode DomType is nonparametric: no degeneracy that adds dimensions (such as refl, sym, or Id) is allowed on a term directly at mode DomType, since that mode's nonparametricity forbids the direction such degeneracies would degenerate.  The codomain mode CodType is unrestricted, as in -functor.

  $ narya -discrete-functor -e "axiom A : DomType axiom a : A synth refl a"
   ￫ error[E1708]
   ￭ command-line exec string
   1 | axiom A : DomType axiom a : A synth refl a
     ^ degeneracy refl is not allowed at mode DomType, which is nonparametric
  
  [1]


  $ narya -discrete-functor -e "axiom A : DomType axiom a : A axiom b : A synth sym (refl a)"
   ￫ error[E1708]
   ￭ command-line exec string
   1 | axiom A : DomType axiom a : A axiom b : A synth sym (refl a)
     ^ degeneracy refl is not allowed at mode DomType, which is nonparametric
  
  [1]


Ordinary (non-degenerate) uses of DomType, including the ○ functor into CodType, are unaffected.

  $ narya -discrete-functor -v -e "def wrap (A :○| DomType) : CodType := data [ circle. (_ :○| A) ]"
   ￫ info[I0000]
   ￮ constant wrap defined
  


At the codomain mode CodType, which is parametric, degeneracies work as usual.

  $ narya -discrete-functor -e "axiom A : CodType axiom a : A synth refl a"
  refl a
    : Id A a a
  

  $ narya -discrete-functor -e "axiom A : CodType axiom a : A synth sym (refl (refl a))"
  sym (refl (refl a))
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
