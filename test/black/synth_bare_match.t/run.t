When a match in a let-binding or anonymous metavariable synthesizes a function type, with at least one of its branches involving a higher comatch, and then is applied to an argument, we would get an anomaly if the metavariable doesn't have its type assigned *before* checking the match, since even though the user can't refer directly to the metavariable, the higher comatch still needs the head to have a type so as to degenerate it.

A match with an explicit motive, applied to arguments inside a case tree, is a convoy: it stays a case-tree node rather than being lifted to a metavariable, so it does not exercise that at all.  It has its own version of the same requirement -- the leading lambdas of its branches belong to the convoy's applications rather than to the head being defined, so descending them must not extend the head's application spine, or the head would be applied beyond its own arity and the higher comatch would again degenerate a self with no type.  The example is kept here because it is the same source text as the ones below, and because it used to be an anomaly on both routes:

  $ narya -v synth_bare_match.ny -e "def k (c : Bool) (x : N) : √N ≔ (match c return z ↦ N → √N [ true. ↦ w ↦ [ .root.e ↦ zero. ] | false. ↦ w ↦ [ .root.e ↦ zero. ] ]) x"
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant √N defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant k defined
  

And to nondependent matches that synthesize a type from one branch:

  $ narya -v synth_bare_match.ny -e "def k (c : Bool) (x : N) : √N ≔ (match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ]) x"
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant √N defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ hint[H0403]
   ￭ command-line exec string
   1 | def k (c : Bool) (x : N) : √N ≔ (match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ]) x
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def k (c : Bool) (x : N) : √N ≔ (match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ]) x
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ info[I0000]
   ￮ constant k defined
  

Including if that synthesizing branch was ascribed:

  $ narya -v synth_bare_match.ny -e "def k (c : Bool) (x : N) : √N ≔ (match c [ true. ↦ (w ↦ [ .root.e ↦ zero. ]) : N → √N | false. ↦ w ↦ [ .root.e ↦ zero. ] ]) x"
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant √N defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ hint[H0403]
   ￭ command-line exec string
   1 | def k (c : Bool) (x : N) : √N ≔ (match c [ true. ↦ (w ↦ [ .root.e ↦ zero. ]) : N → √N | false. ↦ w ↦ [ .root.e ↦ zero. ] ]) x
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def k (c : Bool) (x : N) : √N ≔ (match c [ true. ↦ (w ↦ [ .root.e ↦ zero. ]) : N → √N | false. ↦ w ↦ [ .root.e ↦ zero. ] ]) x
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ info[I0000]
   ￮ constant k defined
  

And if the problematic match is nested inside *another* match:

  $ narya -v synth_bare_match.ny -e "def k (c d : Bool) (x : N) : √N ≔ (match d [ true. ↦ match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ] | false. ↦ match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ] ]) x"
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant √N defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ hint[H0403]
   ￭ command-line exec string
   1 | def k (c d : Bool) (x : N) : √N ≔ (match d [ true. ↦ match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ] | false. ↦ match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ] ]) x
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def k (c d : Bool) (x : N) : √N ≔ (match d [ true. ↦ match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ] | false. ↦ match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ] ]) x
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def k (c d : Bool) (x : N) : √N ≔ (match d [ true. ↦ match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ] | false. ↦ match c [ true. ↦ f | false. ↦ w ↦ [ .root.e ↦ zero. ] ] ]) x
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ info[I0000]
   ￮ constant k defined
  

And if the match appears in a let-binding without ascribed type (in contrast to the others, this is an actually different code path, synth_or_check_let rather than the Match case of Synth):

  $ narya -v synth_bare_match.ny -e "def k (c : Bool) (x : N) : √N ≔ let g ≔ match c return z ↦ N → √N [ true. ↦ w ↦ [ .root.e ↦ zero. ] | false. ↦ w ↦ [ .root.e ↦ zero. ] ] in g x"
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant √N defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant k defined
  

However, it always worked if the entire match is ascribed, since then we end up *checking* the match rather than synthesizing it:

  $ narya -v synth_bare_match.ny -e "def k (c : Bool) (x : N) : √N ≔ (match c return z ↦ N → √N [ true. ↦ w ↦ [ .root.e ↦ zero. ] | false. ↦ w ↦ [ .root.e ↦ zero. ] ] : N → √N) x"
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant √N defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ hint[H0403]
   ￭ command-line exec string
   1 | def k (c : Bool) (x : N) : √N ≔ (match c return z ↦ N → √N [ true. ↦ w ↦ [ .root.e ↦ zero. ] | false. ↦ w ↦ [ .root.e ↦ zero. ] ] : N → √N) x
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant k defined
  

And similarly in the let case:

  $ narya -v synth_bare_match.ny -e "def k (c : Bool) (x : N) : √N ≔ let g : N → √N ≔ match c return z ↦ N → √N [ true. ↦ w ↦ [ .root.e ↦ zero. ] | false. ↦ w ↦ [ .root.e ↦ zero. ] ] in g x"
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant √N defined
  
   ￫ info[I0001]
   ￮ axiom f assumed
  
   ￫ info[I0000]
   ￮ constant k defined
  

The type installed in that metavariable has to be valid outside the match: when a synthesizing branch synthesizes a type that mentions its own pattern variables, that has to be reported as a user error rather than escaping as a readback bug from inside the machinery that installs the type.

  $ narya -v branch_type.ny -e "def k (w : W) : Bool ≔ (match w [ wrap. x ↦ g x | other. ↦ y ↦ b ]) zero."
   ￫ info[I0000]
   ￮ constant N defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant W defined
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0001]
   ￮ axiom g assumed
  
   ￫ info[I0001]
   ￮ axiom b assumed
  
   ￫ hint[H0403]
   ￭ command-line exec string
   1 | def k (w : W) : Bool ≔ (match w [ wrap. x ↦ g x | other. ↦ y ↦ b ]) zero.
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | def k (w : W) : Bool ≔ (match w [ wrap. x ↦ g x | other. ↦ y ↦ b ]) zero.
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ error[E0404]
   ￭ command-line exec string
   1 | def k (w : W) : Bool ≔ (match w [ wrap. x ↦ g x | other. ↦ y ↦ b ]) zero.
     ^ type T x synthesized by synthesizing branch of match is invalid for entire term
  
  [1]
