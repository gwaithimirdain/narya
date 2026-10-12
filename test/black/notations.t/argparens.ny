{` A left-closed notation whose first token also begins a left-open one must be parenthesized when printed as an application argument, since otherwise it would re-parse as the left-open one. `}

axiom A : Type
axiom f : A → A
axiom g : A → A → A
axiom neg : A → A
axiom sub : A → A → A
axiom abs : A → A
axiom bor : A → A → A
axiom a : A
axiom b : A

notation(0) "-" x ≔ neg x
notation(0) x "-" y ≔ sub x y
notation "|" x "|" ≔ abs x
notation(0) x "|" y ≔ bor x y

echo f (- a)
echo g (- a) b
echo g a (- b)
echo f a - b
echo - a
echo f (- (- a))
echo f (| a |)
echo f (| - a |)
echo f a | b
