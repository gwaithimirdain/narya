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
  
