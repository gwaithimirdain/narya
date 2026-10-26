In an application spine, a notation is parenthesized, even when this isn't necessary for parsing, if one of its edges that faces a juxtaposition is a word-like token: the left edge of an argument, the right edge of an argument followed by another argument, or the right edge of a head.

  $ cat >wp.ny <<EOF
  > def B : Type ≔ data [ t. | f. ]
  > axiom a : B
  > axiom b : B
  > axiom c : B
  > axiom g : B → B → B
  > axiom ite : B → B → B → B
  > axiom w : B → B → B
  > axiom id : B → B
  > axiom k : B → B
  > axiom h : B → B → B
  > axiom hs : B → B → B
  > notation "if" x "then" y "else" z "fi" ≔ ite x y z
  > notation "when" x "[" y "]" ≔ w x y
  > notation "⟪" x "⟫" ≔ id x
  > notation "<|" x "done" ≔ k x
  > notation "fun" x "nuf" ≔ h x
  > notation "sel" x "[" "]" ≔ hs x
  > echo g (if a then b else c fi) a
  > echo g a (if a then b else c fi)
  > echo g (when a [ b ]) a
  > echo g a (when a [ b ])
  > echo g ⟪ a ⟫ a
  > echo g (<| a done) a
  > echo g a (<| a done)
  > echo h a b
  > echo hs a b
  > echo g (h a b) c
  > EOF

  $ narya wp.ny
  g (if a then b else c fi) a
    : B
  
  g a (if a then b else c fi)
    : B
  
  g (when a [ b ]) a
    : B
  
  g a (when a [ b ])
    : B
  
  g ⟪ a ⟫ a
    : B
  
  g (<| a done) a
    : B
  
  g a <| a done
    : B
  
  (fun a nuf) b
    : B
  
  sel a [ ] b
    : B
  
  g ((fun a nuf) b) c
    : B
  

The same parentheses are added around a term that solves a hole interactively in such a position, so that ProofGeneral inserts it with them.  Each solve below shows whether the term was parenthesized and its reformatted version.

  $ for c in 'def B : Type ≔ data [ t. | f. ]' 'axiom g : B → B → B' 'axiom k : B → B' 'notation "when" x "[" y "]" ≔ g x y' 'notation "<|" x "done" ≔ k x' 'notation "⟪" x "⟫" ≔ k x' \
  >   'def x0 : B → B ≔ b ↦ g ? t.' 'solve 0 ≔ match b [ t. ↦ t. | f. ↦ f. ]' \
  >   'def x1 : B ≔ g t. ?' 'solve 1 ≔ when t. [ f. ]' \
  >   'def x2 : B ≔ g ? t.' 'solve 2 ≔ <| t. done' \
  >   'def x3 : B ≔ g t. ?' 'solve 3 ≔ <| t. done' \
  >   'def x4 : B ≔ g ? t.' 'solve 4 ≔ ⟪ when t. [ f. ] ⟫' \
  >   'def x5 : B ≔ g t. ?' 'solve 5 ≔ (when t. [ f. ])' \
  >   'def x6 : B → B ≔ b ↦ ?' 'solve 6 ≔ match b [ t. ↦ t. | f. ↦ f. ]'; do printf '%s\n\f\n' "$c"; done > input

  $ narya -proofgeneral < input | tr '\f' '\n' | awk '/hole solved/ { s = 1 } /^(un)?parenthesized$/ { p = $0 } s && r && $0 != "" { print p ": " $0; s = 0 } { r = ($0 == "[reformat]") || (r && $0 == "") }'
  parenthesized: (match b [ t. ↦ t. | f. ↦ f. ])
  parenthesized: (when t. [ f. ])
  parenthesized: (<| t. done)
  unparenthesized: <| t. done
  unparenthesized: ⟪ when t. [ f. ] ⟫
  unparenthesized: (when t. [ f. ])
  unparenthesized: match b [ t. ↦ t. | f. ↦ f. ]
