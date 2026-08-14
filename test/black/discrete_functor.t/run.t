The -discrete-functor mode theory is like -functor, but its domain mode DomType is nonparametric: no degeneracy that adds dimensions (such as refl, sym, or Id) is allowed on a term directly at mode DomType, since that mode's nonparametricity forbids the letter s, nameuch degeneracies would degenerate.  The codomain mode CodType is unrestricted, as in -functor.

  $ narya -e "option parametric ≔ arity 2, letter p, name rel Br option modal ≔ discrete functor axiom A : DomType axiom a : A synth rel a"
   ￫ error[E1708]
   ￭ command-line exec string
   1 | option parametric ≔ arity 2, letter p, name rel Br option modal ≔ discrete functor axiom A : DomType axiom a : A synth rel a
     ^ degeneracy rel is not allowed at mode DomType, which is nonparametric
  
  [1]


  $ narya -e "option parametric ≔ arity 2, letter p, name rel Br option modal ≔ discrete functor axiom A : DomType axiom a : A axiom b : A synth sym (rel a)"
   ￫ error[E1708]
   ￭ command-line exec string
   1 | option parametric ≔ arity 2, letter p, name rel Br option modal ≔ discrete functor axiom A : DomType axiom a : A axiom b : A synth sym (rel a)
     ^ degeneracy rel is not allowed at mode DomType, which is nonparametric
  
  [1]


Ordinary (non-degenerate) uses of DomType, including the ○ functor into CodType, are unaffected.

  $ narya -v -e "option parametric ≔ arity 2, letter p option modal ≔ discrete functor def wrap (A :○| DomType) : CodType := data [ circle. (_ :○| A) ]"
   ￫ info[I0000]
   ￮ constant wrap defined
  


At the codomain mode CodType, which is parametric, degeneracies work as usual.

  $ narya -e "option parametric ≔ arity 2, letter p, name rel Br option modal ≔ discrete functor axiom A : CodType axiom a : A synth rel a"
  rel a
    : Br A a a
  

  $ narya -e "option parametric ≔ arity 2, letter p, name rel Br option modal ≔ discrete functor axiom A : CodType axiom a : A synth sym (rel (rel a))"
  sym (rel (rel a))
    : A⁽ᵖᵖ⁾ (rel a) (rel a) (rel a) (rel a)
  
