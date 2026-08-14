option parametric ≔ arity 2, letter p, name rel Br

axiom A : Type

axiom B : Type

echo B

def id : Type → Type ≔ X ↦ X

axiom b : B

axiom g : (A → B) → A → B

def f : A → B ≔ g ¿ g f ! _ ↦ ? ʔ

axiom a_very_long_variable : A

axiom a_very_long_function : A → A → A → A → A → A → A → B

def f' : A → B ≔ ?

{` Check whether notations that were in scope at the time of a hole are still available when solving the hole even if they're no longer in scope at the current time, while notations defined later are not in scope for the hole. `}
section sec ≔

  notation "&" ≔ b

  def f' : A → B ≔ ¿_ ↦ &ʔ

end

notation "$" ≔ b

def ℕ : Type ≔ data [ zero. : ℕ | suc. : ℕ → ℕ ]

def plus (m n : ℕ) : ℕ ≔ match n [ zero. ↦ ? | suc. n ↦ ? ]

axiom P : ℕ → Type

def anop : ℕ → ℕ → (x : ℕ) → P x ≔ n n′ n ↦ ?

{` The user's "n′" should not be shadowed by an auto-generated one `}
def anop' : ℕ → ℕ → (x : ℕ) → P x ≔ n′ n n ↦ ?

def anop'' : ℕ → ℕ → (x : ℕ) → P x ≔ n _ n ↦ ?

{` Nor the user's 𝑥 be shadowed by an auto-generated one `}
def anop''' : ℕ → ℕ → (x : ℕ) → P x ≔ 𝑥 _ n ↦ ?

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

{` Here the type of the second hole is not the first hole but "pp .fst", since the first hole is potential and causes its case tree to be just stuck. `}
def pp : Σ Type (X ↦ X) ≔ (?, ?)

{` But if we break the case tree, then the type of the second hole is the first hole. `}
def pp' : Σ Type (X ↦ X) ≔ (id ?, ?)

{` The out-of-scope variable "𝑥" that appears here is because record types are stored internally like codatatypes with all fields depending on a single variable, so we have to introduce that variable during typechecking. `}
def foo : Type ≔ sig (
  bar : ℕ,
{` It's important for ? to be its own token, so that it can be followed immediately by a comma. `}
  baz : ? )

def foo' : Type ≔ sig ( bar : Type, baz : (x : bar) → ? )

def gel0 (A B : Type) : Br Type A B ≔ sig ( x .one : ? )

def gel1 (A B : Type) : Br Type A B ≔ sig ( x .one : Type, x .two : ? )

def gel2 (A B : Type) : Br Type A B ≔ sig ( x .one : ?, x .two : ? )

def gel3 (A B : Type) : Br Type A B ≔ codata [
| x .one : ?
| x .two : ? ]

axiom C : A → Type

def AC : Type ≔ sig ( a : ℕ → A, c : C (a zero.) )

def ac : AC ≔ (a ≔ ?, c ≔ ?)

def ida : A → A ≔ x ↦ x

def ideqid : Br (A → A) ida ida
  ≔ ((x ↦ x) : Br (A → A) ida ida → Br (A → A) ida ida) ({u} {u} u ↦ u)

echo ideqid

{` TODO: Ideally, the user's "u′" should not be shadowed by an auto-generated one (although this matters a bit less than the one for contexts, since the user won't be using it to enter terms).  (This isn't about holes.) `}
def ideqid' : Br (A → A) ida ida
  ≔ ((x ↦ x) : Br (A → A) ida ida → Br (A → A) ida ida) ({u} {u} u′ ↦ u′)

echo ideqid'

def ideqid'' : Br (A → A) ida ida
  ≔ ((x ↦ x) : Br (A → A) ida ida → Br (A → A) ida ida) ({u} {u} u ↦ ?)

{` A kinetic hole `}
def afam : Type → Type ≔ X ↦ id ?

{` This requires comparing a metavariable to equal itself when evaluated in equal environments. `}
def idafam (X : Type) : afam X → afam X ≔ x ↦ x

{` For testing hole splitting `}

axiom f0 : A → B
def f2 : Br ((x : A) → B) f0 f0 ≔ x ⤇ ?

def prod : Type ≔ sig ( fst : A, snd : B )
def p : prod ≔ ?

axiom p0 : prod
def p2 : Br prod p0 p0 ≔ ?

def prod' : Type ≔ codata [ x .fst : A | x .snd : B ]
def p : prod' ≔ ?
