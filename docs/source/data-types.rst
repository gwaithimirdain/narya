Inductive datatypes and matching
================================

Defining datatypes
------------------

An inductive datatype is defined by a number of *constructors*, each with a declared type that must be an iterated function-type whose eventual codomain is the datatype itself.  A constant of type ``Type`` can be defined to be a datatype in a ``def`` statement by using the keyword ``data`` and listing the constructors with their types in square brackets, separated by bars.  For instance, we can define the booleans:

.. code-block:: none

   def Bool : Type ≔ data [
   | true. : Bool
   | false. : Bool
   ]

The ``|`` before the first constructor is optional, and no spaces are required around the brackets and bar (unless, as usual, the bar is adjacent to a notation involving other special ASCII symbols).

Note that each constructor ends with a period.  This is intentionally dual to the fact that record fields (and codata methods, see below) *begin* with a period, and reminds us that constructors, like fields and records, are not namespaced but belong to a separate flat name domain.  (OCaml programmers should think of polymorphic variants, not regular variants, although there is no subtyping yet.)  The use of separate syntax distinguishing constructors from variables and functions is also familiar from functional programming, although the specific use of a dot suffix is unusual (capitalization is more common).

Also as with record types, this is not defining ``Bool`` to equal a pre-existing thing, but declaring it to be a new type that didn't previously exist and doesn't reduce to anything else.

Datatypes can have parameters:

.. code-block:: none

   def Sum (A B : Type) : Type ≔ data [
   | inl. : A → Sum A B
   | inr. : B → Sum A B
   ]

As with records, this is equivalent to

.. code-block:: none

   def Sum : Type → Type → Type ≔ A B ↦ data [
   | inl. : A → Sum A B
   | inr. : B → Sum A B
   ]

When there are parameters, the output type must be the datatype applied to those same parameters.

The arguments of each constructor can also be written as parameters before its colon:

.. code-block:: none

   def Sum (A B : Type) : Type ≔ data [
   | inl. (a : A) : Sum A B
   | inr. (b : B) : Sum A B
   ]

When all the arguments (if any) are written this way, the output type can be omitted since we know what it must be (the datatype being defined):

.. code-block:: none

   def Sum (A B : Type) : Type ≔ data [
   | inl. (a : A)
   | inr. (b : B)
   ]

Of course, we can introduce a notation for this type after it is defined:

.. code-block:: none

   notation 1 Sum : A "⊔" B ≔ Sum A B

But it is not currently possible to use a notation during the definition.

Datatypes can be recursive, meaning the inputs of a constructor can involve the datatype itself.  For instance, we have the natural numbers:

.. code-block:: none

   def ℕ : Type ≔ data [
   | zero.
   | suc. (_ : ℕ)
   ]

and the type of lists:

.. code-block:: none

   def List (A:Type) : Type ≔ data [
   | nil.
   | cons. (x : A) (xs: List A)
   ]

For consistency, such occurrences should be strictly positive, but this is not yet checked.  The parameters of a recursive datatype can be "non-uniform", meaning that occurrences of the datatype in the inputs of a constructor (as opposed to the output) can be applied to different parameters.

A datatype can have zero constructors, yielding an empty type:

.. code-block:: none

   def ⊥ : Type ≔ data [ ]

Finally, a datatype can also have *indices*, which are arguments of its type that are not abstracted over (either as parameters, or with ↦ after the ≔) before issuing the ``data`` keyword.  In this case, all the constructors must include an explicit output type that specifies the values of the indices for that constructor (and also includes all the parameters explicitly, although these cannot differ between constructors).  For instance, we have vectors (length-indexed lists):

.. code-block:: none

   def Vec (A:Type) : ℕ → Type ≔ data [
   | nil. : Vec A zero.
   | cons. : (n:ℕ) → A → Vec A n → Vec A (suc. n)
   ]

As always for parameters of ``def``, this is equivalent to 

.. code-block:: none

   def Vec : Type → ℕ → Type ≔ A ↦ data [
   | nil. : Vec A zero.
   | cons. : (n:ℕ) → A → Vec A n → Vec A (suc. n)
   ]

In particular, in the latter case ``A`` is still a parameter in the datatype sense, even though it does not appear to the left of the typing colon for ``Vec``, because it is abstracted over before the ``data`` keyword.

The other classic example of a datatype with an index is the "Jdentity" type, in either Martin-Löf style:

.. code-block:: none
   
   def Jd (A:Type) : A → A → Type ≔ data [
   | rfl. (a:A) : Jd A a a
   ]

or Paulin-Möhring style:

.. code-block:: none

   def Jd (A:Type) (a:A) : A → Type ≔ data [
   | rfl. : Jd A a a
   ]

Applying constructors
---------------------

A constructor, meaning an identifier ending with a period but containing no internal periods, can be applied to some number of arguments like a function, and then typechecked at a datatype that contains such a constructor.  For instance, ``zero.`` and ``suc. zero.`` and ``suc. (suc. zero.)``` all typecheck at ``ℕ``.

Constructors check rather than synthesizing.  As usual with checking terms, one constructor application can check at many different datatypes.  As a simple and common example, ``nil.`` typechecks at ``List A`` for *any* type ``A``.  This makes it clear that, unlike an ordinary function application, a constructor application cannot synthesize, as there is no way to guess from ``nil.`` what the type ``A`` should be.  Moreover, unlike in some other languages, the parameter ``A`` is not even an "implicit argument" of the constructor; the only way to make ``nil.`` synthesize is to ascribe it as ``nil. : List A``.  Similarly, ``inl. a`` typechecks at ``A ⊔ B`` for any type ``B``.

Constructors must always be applied to all of their arguments.  For instance, one cannot write ``cons. x : List A → List A``.  You have to η-expand it: ``(xs ↦ cons. x xs) : List A → List A``.  This might be improved in future.


Numeral notations
-----------------

Natural number literals such as ``0``, ``7``, and ``23`` are expanded at parse time into applications of the constructors ``suc.`` and ``zero.``.  There is no built-in datatype with these constructors, but of course the user can define ``ℕ`` as above, in which case for instance ``3 : ℕ`` is equivalent to ``suc. (suc. (suc. zero.))``.  But numerals will also typecheck at any other datatype having constructors of the same name.

Decimal number literals such as ``0.5`` and ``2.3`` are similarly expanded at parse time into the constructor ``quot.`` applied to a numerator and denominator, where the numerator is a natural number obtained through applications of ``suc.`` and ``zero.``, while the denominator is a "positive natural number" obtained through applications of ``suc.`` and ``one.``.  Such fractions are reduced to lowest terms before this translation is applied, so for instance ``0.5`` becomes ``quotsuc. (suc. zero.) (suc. one.)``, while ``0.75`` becomes ``quot. (suc. (suc. (suc. zero.))) (suc. (suc. (suc. one.)))``.  Again, there is no built-in datatype with these constructors, but the user can define for instance

.. code-block:: none

   def ℕ₊ : Type ≔ data [ one. | suc. (_ : ℕ₊) ]
   def ℚ₀₊ : Type ≔ data [ zero. | suc. (_ : ℕ) | quot. (_ : ℕ) (_ : ℕ₊) ]

Of course this is not a correct representation of non-negative rational numbers without either an extra parameter of ``quot.`` ensuring that the fraction is in lowest terms or a higher constructor that equates equal fractions, neither of which can be implemented yet.  Also note that mathematically, the constructors ``zero.`` and ``suc.`` are redundant since ``quot. n one.`` also embeds the natural numbers, but are currently necessary for whole number literals to typecheck at ``ℚ₀₊`` since they are translated using ``suc.`` and ``zero.``.

Decimal literals must include at least one digit both before and after the decimal point, since otherwise they would be parsed as a field projection or an ordinary constructor application.  There is no difference between `2` and `2.0`; in particular, both will typecheck at ``ℕ``.

Natural number and positive natural number numerals, composed of the constructors ``zero.``, ``suc.`` and ``one.``, are printed in the expected way.  Decimal numbers are not printed specially, but fractions can be both parsed and printed with an ordinary notation definition for the ``quot`` constructor:

.. code-block:: none

   notation 0 quot : x "/" y ≔ quot. x y

This will cause ``1/2`` to parse into ``quot. (suc. zero.) (suc. one.)``, and also ``quot. (suc. zero.) (suc. one.)`` to be printed as ``1 / 2``.  It also results in ``0.5`` being printed as ``1 / 2``, while ``1/0`` does not typecheck since ``ℕ₊`` has no constructor ``zero.``.  It doesn't permit division of arbitrary rational numbers; you can allow the "numerator" of the constructor ``quot.`` to be an arbitrary rational (with a higher field expected), but of course the denominator can't be anything that might be zero.

Matching
--------

When a new constant is defined as a function with arguments that belong to datatypes, it can match on such an argument (called the *discriminee*).  For instance, the function that swaps the elements of a binary sum can be written as

.. code-block:: none

   def Sum.swap (A B : Type) (x : A ⊔ B) : B ⊔ A ≔ match x [
   | inl. a ↦ inr. a
   | inr. b ↦ inl. b
   ]

The ``|`` before the first branch is optional.  Each branch is determined by one of the constructors of the datatype applied to distinct new "pattern variables" that are then bound in the body of that branch.  The body can then proceed to match again on these variables or on other variables.  For instance, we have associativity of sums:

.. code-block:: none

   def Sum.assoc (A B C : Type) (x : (A ⊔ B) ⊔ C) : A ⊔ (B ⊔ C) ≔ match x [
   | inl. y ↦ match y [
     | inl. a ↦ inl. a
     | inr. b ↦ inr. (inl. b)
     ]
   | inr. c ↦ inr. (inr. c)
   ]

By omitting the keyword ``match`` and the variable name, it is possible to abstract over a variable and simultaneously match against it (pattern-matching lambda abstraction).  Thus, ``Sum.swap`` can equivalently be defined as

.. code-block:: none

   def Sum.swap (A B : Type) : A ⊔ B → B ⊔ A ≔ [
   | inl. a ↦ inr. a
   | inr. b ↦ inl. b 
   ]

A match (of this simple sort) is a checking term.  It requires the term being matched against to synthesize, while the bodies of each branch are checking (we will discuss below how the type they are checked against is determined).


Matching and case trees
-----------------------

Matches are case tree nodes, which only reduce if the term being matched against is a constructor form so that one of the branches can be selected.  Thus, for instance, ``Sum.swap x`` does not reduce unless ``x`` is a constructor, and similarly for ``Sum.assoc (inl. x)``.  This more or less aligns with the behavior of functions defined by pattern-matching in Agda, whereas Coq has to mimic it with ``simpl nomatch`` annotations.

However, unlike the other types and constructs we have discussed so far, matches and datatypes do not satisfy any kind of η-conversion.  Thus, two functions defined by matching are not equal to each other even if their definitions are identical.  For instance, if we define

.. code-block:: none

   def neg1 : Bool → Bool ≔ [ true. ↦ false. | false. ↦ true. ]
   def neg2 : Bool → Bool ≔ [ true. ↦ false. | false. ↦ true. ]

then ``neg1`` and ``neg2`` are not convertible.  By η-expansion, when trying to convert them we do automatically introduce a new variable ``x`` and try to compare ``neg1 x`` with ``neg2 x``, but neither of these terms reduce since ``x`` is not a constructor.  In particular, datatypes do not satisfy any kind of η-conversion themselves.


Recursion
---------

A function defined by matching can also be recursive, calling itself in each branch.  For instance, we have addition of natural numbers (in one of the possible ways):

.. code-block:: none

   def ℕ.plus (m n : ℕ) : ℕ ≔ match m [
   | zero. ↦ n
   | suc. m ↦ suc. (ℕ.plus m n)
   ]

   notation 4 ℕ.plus : x "+" y ≔ ℕ.plus x y

To ensure termination and consistency, the recursive calls should be on structurally smaller arguments.  But currently there is no checking for this, so it is possible to write infinite loops.  In fact this is possible even without matching:

.. code-block:: none

   def oops : ⊥ ≔ oops

(In this connection, recall that ``echo`` fully normalizes its argument before printing it, so ``echo oops`` will loop forever.  By contrast, this does not usually happen with infinite loops guarded by a ``match``, because matches are case tree nodes, so their branch bodies are not normalized unless their argument is a constructor that selects a particular branch.)

While there is no termination-checking there is coverage-checking.  Thus, all the constructors of a datatype must be present in the match.  So while you can write infinite loops, your programs shouldn't get stuck.


Multiple matches and deep matches
---------------------------------

It is possible to condense a sequence of nested matches into a single one.  For example, the above definition of ``Sum.assoc`` can be condensed into a single "deep match":

.. code-block:: none

   def Sum.assoc (A B C : Type) (x : (A ⊔ B) ⊔ C) : A ⊔ (B ⊔ C) ≔ match x [
   | inl. (inl. a) ↦ inl. a
   | inl. (inr. b) ↦ inr. (inl. b)
   | inr. c        ↦ inr. (inr. c)
   ]

Similarly, a naive definition of the Boolean conjunction would be:

.. code-block:: none

   def andb (x y : Bool) : Bool ≔ match x [
   | true.  ↦ match y [
     | true.  ↦ true.
     | false. ↦ false.
     ]
   | false. ↦ false.
   ]

but this can be condensed to a "multiple match":

.. code-block:: none

   def andb (x y : Bool) : Bool ≔ match x, y [
   | true.  , true.  ↦ true.
   | true.  , false. ↦ false.
   | false. , _      ↦ false.
   ]

Here the ``_`` indicates that that value can be anything.  It can also be replaced by a variable, which is then bound to the value being matched.

Multiple and deep matches can be combined.  In general, for a multiple match on a comma-separated list of a positive number of discriminees, the left-hand side of each branch must be a comma-separated list of the same number of *patterns*.  Each pattern is either a variable, an underscore, or a constructor applied to some number of other patterns.  Plain variable patterns are equivalent to let-bindings: ``match x [ y ↦ M ]`` is the same as ``let y ≔ x in M``.  Multiple and deep matches are (with one exception, discussed below) a *purely syntactic* abbreviation: the condensed forms are expanded automatically to the nested match forms before even being typechecked.

Multiple and deep patterns can also be used in pattern-matching abstractions.  In the case of a multiple match, the number of variables abstracted over is determined by the number of patterns in the branches.  Thus, for instance, ``andb`` can also be defined by:

.. code-block:: none

   def andb : Bool → Bool → Bool ≔ [
   | true.  , true.  ↦ true.
   | true.  , false. ↦ false.
   | false. , _      ↦ false.
   ]

All the pattern variables of each branch must be distinct: they cannot shadow each other.  Allowing them to shadow each other would be a recipe for confusion, because replacing a match by its expanded version alters the order in which variables appear.  For instance, the nested match

.. code-block:: none

   def prod' (A B : Type) : Type ≔ data [ pair. (_:A) (_:B) ]

   def proj31 (A B C : Type) (u : prod' (prod' A B) C) : A ≔ match u [
   | pair. (pair. x y) z ↦ x
   ]

would expand to

.. code-block:: none

   def proj31 (A B C : Type) (u : prod' (prod' A B) C) : A ≔ match u [
   | pair. H z ↦ match H [
     | (pair. x y) ↦ x
     ]
   ]

in which ``z`` is bound first instead of last.  (The intermediate variable ``H`` is inserted automatically in the process of expansion, and you will see it in the contexts of holes.)

Matching always proceeds from left to right, so that the matches corresponding to the leftmost discriminee will be on the outside and those corresponding to the rightmost discriminee will be on the inside.  Of course, you can re-order the top-level discriminees as you wish when writing a match (an advantage over Agda's pattern-matching).  However, if a constructor has multiple arguments which are then matched against deeply, these matches also proceed from left to right, and this cannot be changed within a single multi/deep match.  For example:

.. code-block:: none

   def andb2 (x : prod' Bool Bool) : Bool ≔ match x [
   | pair. true. true.   ↦ true.
   | pair. true. false.  ↦ false.
   | pair. false. true.  ↦ false.
   | pair. false. false. ↦ false.
   ]

Here the first argument of ``pair.`` is matched before the second, producing the following expanded form:

.. code-block:: none

   def andb2 (x : prod' Bool Bool) : Bool ≔ match x [
   | pair. a b ↦ match a [
     | true. ↦ match b [
       | true. ↦ true.
       | false. ↦ false.
       ]
     | false. ↦ match b [
       | true. ↦ false.
       | false. ↦ false.
       ]
     ]
   ]

To match on the second argument first, you would have to use a nested match explicitly:

.. code-block:: none

   def andb2' (x : prod' Bool Bool) : Bool ≔ match x [
   | pair. a b ↦ match b, a [
     | true.  , true.  ↦ true.
     | false. , true.  ↦ false.
     | true.  , false. ↦ false.
     | false. , false. ↦ false.
     ]
   ]

The patterns in a match are not allowed to overlap.  This is in contrast to Agda, which accepts the following definition

.. code-block:: none

   -- This is Agda, not Narya
   max : Nat → Nat → Nat
   max zero    n       = n
   max m       zero    = m
   max (suc m) (suc n) = suc (max m n)

The analogous Narya code

.. code-block:: none

   {` Not valid! `}
   def max (x y : ℕ) : ℕ ≔ match x, y [
   | zero. , n ↦ n
   | m , zero. ↦ m
   | suc. m, suc. n ↦ suc. (max m n)
   ]

produces an error message about overlapping cases.  You have to write instead

.. code-block:: none

   def max (x y : ℕ) : ℕ ≔ match x, y [
   | zero. , n ↦ n
   | suc. m, zero. ↦ x
   | suc. m, suc. n ↦ suc. (max m n)
   ]

so that it can be expanded to the nested match

.. code-block:: none

   def max (x y : ℕ) : ℕ ≔ match x [
   | zero. ↦ y
   | suc. m ↦ match y [
     | zero. ↦ x
     | suc. n ↦ suc. (max m n) 
     ]
   ]

In fact, this expansion is also what Agda does internally, even when presented with the first definition above (see the `Agda manual <https://agda.readthedocs.io/en/v2.6.4.3-r1/language/function-definitions.html#case-trees>`_).  This means that in Agda, not all the clauses in such a definition may hold definitionally, e.g. ``max m zero`` is not convertible with ``m`` when ``m`` is a variable.  For this reason Agda has the ``--exact-split`` flag that prevents such clauses.  Narya *always* insists on "exact splits", and this is unlikely to change: we regard it as a feature.


Empty types and refutation cases
--------------------------------

As is well-known, it can be tricky to deal with empty types in multiple and deep matches.  A naive extension of the treatment of nonempty types can cause information to disappear, and while sometimes this information can be reconstructed, other times it must be indicated explicitly.  As a first example, consider the following function defined by nested matches:

.. code-block:: none

   def foldinl (x : (A ⊔ A) ⊔ ⊥ ) : A ≔ match x [
   | inl. u ↦ match u [
     | inl. a ↦ a
     | inr. a ↦ a
     ]
   | inr. v ↦ match v [ ]
   ]

If we rewrite this as a deep match, each branch of the outer match should be replaced by one branch for *each branch* of the corresponding inner match; but since the inner match on ``v`` has *zero* branches, this causes the outer branch with pattern ``inr. v`` to disappear completely:

.. code-block:: none

   def foldinl (x : (A ⊔ A) ⊔ ⊥ ) : A ≔ match x [
   | inl. (inl. a) ↦ a
   | inl. (inr. a) ↦ a
   ]

In this example, this is not a problem, because Narya (like other proof assistants) can recognize from the type of ``x`` *and the fact that there is at least one* ``inl`` *branch* that there should also be an ``inr`` branch — and once there is an ``inr`` branch, it is straightforward to notice that the argument of ``inr`` is empty and thus can be matched against without needing any further branches.

This also works for multiple matches:

.. code-block:: none

   def P : A ⊔ B → Type ≔ [ inl. _ ↦ ⊤ | inr. _ ↦ ⊥ ]

   def foo (u : A ⊔ B) (v : P u) : A ≔ match u, v [
   | inl. a, _ ↦ a
   ]

Again the presence of an ``inl`` branch clues Narya in that there should also be an ``inr`` branch, and then it can notice that in this branch the type of ``v`` becomes empty.  The order of variables doesn't matter either:

.. code-block:: none

   def foo' (u : A ⊔ B) (v : P u) : A ≔ match v, u [
   | _, inl. a ↦ a
   ]

In general, when cases for one or more constructors are obviously missing from a match, Narya will inspect all the pattern variables and discriminees that would be available in that branch, and if it finds one whose type is empty, it inserts a match against that term.  Here by "empty" we mean that it was literally declared as a datatype with no constructors: there is no unification like in Agda to rule out impossible indices (although see the remarks about canonical types defined by case trees, below).  This is the exception mentioned above in which the expansion of multiple and deep matches requires some typechecking information: namely, whether the type of some variable is an empty datatype.

As a particular case, if any of the discriminees belong directly to an empty datatype, then all the branches can be omitted.  Similarly, an empty pattern-matching lambda abstraction ``[ ]`` can be a multivariable function, although in this case there are no branches to indicate the number of arguments; instead Narya inspects the possibly-iterated function type it is being checked at, looking through the domains one at a time until it finds an empty one.  Thus the following are both valid:

.. code-block:: none

   def bar (x : Bool) (y : ⊥) : ⊥ ≔ match x, y [ ]
   
   def bar' : Bool → ⊥ → ⊥ ≔ [ ]


However, Narya will not perform *additional* matches in order to expose an inhabitant of an empty datatype (this is probably an undecidable problem in general).  For example, consider the following nested match:

.. code-block:: none

   def abort2 (u : ⊥ ⊔ ⊥) : A ≔ match u [
   | inl. e ↦ match e [ ]
   | inr. e ↦ match e [ ]
   ]

Rewriting this naïvely as as nested match would produce one with *zero* branches, but trying to write such a match directly fails:

.. code-block:: none

   def abort2 (u : ⊥ ⊔ ⊥) : A ≔ match u [ ]
   
     ￫ error[E1300]
     1 | def abort2 (u : ⊥ ⊔ ⊥) : A ≔ match u [ ]
      ^ missing match clause for constructor inl

This is because in the absence of either an ``inl`` or an ``inr`` branch, and because the type of ``u`` is not syntactically empty (semantically it is empty, but it is not declared as a datatype with zero constructors), Narya can't guess that ``u`` has to be matched against in order to expose variables of type ⊥.

One solution to this, of course, is to write the nested match.  In fact, only one of its branches is needed, as then the other can be inferred:

.. code-block:: none

   def abort2 (u : ⊥ ⊔ ⊥) : A ≔ match u [
   | inl. e ↦ match e [ ]
   ]

Another solution is to use a *refutation case*: if the body of a branch is a single dot ``.`` then Narya will search all of its pattern variables for one belonging to an empty type:

.. code-block:: none

   def abort2 (u : ⊥ ⊔ ⊥) : A ≔ match u [
   | inl. _ ↦ .
   | inr. _ ↦ .
   ]

And, again, only one branch is necessary:

.. code-block:: none

   def abort2 (u : ⊥ ⊔ ⊥) : A ≔ match u [
   | inl. _ ↦ .
   ]

Variable matches
----------------

There are several variations of matching based on how type information flows and is refined.  Probably the most important kind of matching is when the discriminee is a free variable that belongs to a datatype instance whose indices are distinct free variables not occurring in any of the parameters, and the match is in a checking context.  In this case, the output type *and* the types of all other variables in the context are *refined* while checking each branch of the match, by substituting the corresponding constructor applied to its pattern variables, and its corresponding indices, for these free variables.  This is similar to the behavior of Agda when splitting a definition on a variable.

For example, we can prove that natural number addition is associative:

.. code-block:: none

   def ℕ.plus.assoc (m n p : ℕ) : Id ℕ ((m+n)+p) (m+(n+p)) ≔ match m [
   | zero. ↦ refl (n+p)
   | suc. m' ↦ suc. (ℕ.plus.assoc m' n p)
   ]

This proof uses observational identity types, which are introduced below.  But the point here is that in the ``suc.`` branch, the variable ``m`` is defined to equal ``suc. m'``, and this definition is substituted into the goal type ``Id ℕ ((m+n)+p) (m+(n+p))``, causing both additions to reduce one step.  You can see this by inserting a hole in this clause:

.. code-block:: none

   def ℕ.plus.assoc (m n p : ℕ) : Id ℕ ((m+n)+p) (m+(n+p)) ≔ match m [
   | zero. ↦ refl (n+p)
   | suc. m' ↦ ?
   ]
   
        hole ?0 generated:
        
        n : ℕ
        p : ℕ
        m' : ℕ
        m ≔ suc. m' : ℕ
        ----------------------------------------------------------------------
        refl ℕ (suc. ((m' + n) + p)) (suc. (m' + (n + p)))

As an example with indices, we can define appending of vectors:

.. code-block:: none

   def Vec.append (A : Type) (m n : ℕ) (v : Vec A m) (w : Vec A n) : Vec A (ℕ.plus m n) ≔ match v [
   | nil. ↦ w
   | cons. k a u ↦ cons. (ℕ.plus k n) a (Vec.append A k n u w)
   ]

Here the match against ``v`` falls into this case of matching because ``v`` and the index ``m`` of its type ``Vec A m`` are both free variables.  Then in the two branches, not only is ``v`` specialized to the constructor, the variable ``m`` is also specialized to the index value associated to that constructor, namely ``zero.`` in the first branch and ``suc. k`` in the second.  Again, you can see this with a hole:

.. code-block:: none

   def Vec.append (A : Type) (m n : ℕ) (v : Vec A m) (w : Vec A n) : Vec A (ℕ.plus m n) ≔ match v [
   | nil. ↦ w
   | cons. k a u ↦ ?
   ]
   
        hole ?1 generated:
        
        A : Type
        n : ℕ
        w : Vec A n
        k : ℕ
        m ≔ suc. k : ℕ
        a : A
        u : Vec A k
        v ≔ cons. k a u : Vec A (suc. k)
        ----------------------------------------------------------------------
        Vec A (suc. (k + n))

(Note that the body of the second branch typechecks because ``ℕ.plus (suc. k) n`` reduces to ``suc. (ℕ.plus k n)``, which is why we defined addition of natural numbers as we did.  The other addition of natural numbers, by recursion on the second argument, instead aligns with appending of *backwards* vectors.)

The fact that the indices cannot occur in the parameters prevents us, for instance, from proving Axiom K.  Thus it is even less general than Agda's ``--without-K`` matching, and hence also ensures consistency with univalence.  In the future we may implement a more general unification-based condition like Agda's.


Non-dependent matches
---------------------

It is also possible to match against a term that is not a free variable, or whose indices are not distinct free variables or occur in the parameters.  In this case Narya cannot guess how to refine the output type or other variables in the context, so it doesn't.  The term being matched against is not defined to equal anything (that doesn't even make sense); instead the pattern variables in each branch are simply introduced as new free variables unrelated to any previous ones, and the output type remains the same in each branch.  As a simple example, we can prove *ex falso quodlibet* without a helper function:

.. code-block:: none

   def ⊥ : Type ≔ data [ ]
   
   def efq (A C : Type) (a : A) (na : A → ⊥) : C ≔ match na a [ ]

Note that matching against a let-bound variable is equivalent to matching against its value, so it falls under this category.

The fact that this kind of match uses the same syntax as the previous one means that if you intend to do a variable match, as above, but the conditions on the match variable and its indices are not satisfied, then Narya will fall back to trying this kind of match.  You will then probably get an error message due to the fact that the goal type didn't get refined in the branches the way you were expecting it to.  Narya tries to help you find bugs of this sort by emitting a hint when that sort of fallback happens.  If you really did mean to write a non-dependent match, you can silence the hint by writing ``match M return _ ↦ _`` (see the next sort of match, below).

A variable match can only check, but a non-dependent match can also synthesize.  This requires at least one of the branch bodies to synthesize a type that does not depend on any of its pattern variables; then the other branches are checked against that same type, and it is the type synthesized by the whole match statement.  Writing a match that could have been a variable match but in a synthesizing context will also cause an automatic fallback to non-dependent matching, with a hint emitted.

Like the ordinary ``match`` command, a pattern-matching abstraction like ``def pred : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ n ]`` always attempts to generate a match against a variable, and falls back to a non-dependent match if this fails (e.g. if the domain does not have fully general indices).


Explicitly dependent matches
----------------------------

Although Narya can't guess how to refine the output type when matching against a general term, you can tell it how to do so by writing ``match M return x ↦ P``.  Here ``x ↦ P`` (where ``P`` can involve ``x``) is a type family (called the *motive*) depending on a variable ``x`` belonging to the datatype (the type of ``M``).  If this datatype has indices, then variables to be bound to the indices must be included in the abstraction as well, e.g. ``match V return i v ↦ P`` for matching against a vector; this ensures that the motive of the elimination is fully general over the indexed datatype family.  Thus, this kind of match has roughly the same functionality as Coq's ``match M in T i as x return P``.

Each branch of such a match is checked at the type obtained by substituting the corresponding constructor for ``x`` in the motive ``P``.  The entire match synthesizes the result of substituting the discriminee ``M`` for ``x`` in the motive ``P``.  For example, we could prove associativity of addition more verbosely as follows:

.. code-block:: none

   def ℕ.plus.assoc (m n p : ℕ) : Id ℕ ((m+n)+p) (m+(n+p))
     ≔ match m return x ↦ Id ℕ ((x+n)+p) (x+(n+p)) [
     | zero. ↦ refl (n+p)
     | suc. m' ↦ suc. (ℕ.plus.assoc m' n p)
     ]

As usual, the variables bound in the motive can be written as underscores if they are not used; thus with ``match M return _ ↦ P`` you can specify a constant motive explicitly.  This is equivalent to ascribing the entire match to type ``P``, but it forces the match to be a non-dependent one.  You can also write ``match M return _ ↦ _`` in a checking context (with the correct number of variables for the indices, if any) to indicate that the output type is intentionally constant, silencing any hints about fallback, without having to specify that output type explicitly.

A match with an explicit motive cannot have more than one discriminee.  It would be rather complicated to work out, and indicate syntactically, the dependence of such a motive on all the discriminees.  Of course, you can write your own nested sequence of matches.  However, deep matching on one discriminee is still available with an explicit motive.  Upon expansion, only the outermost match will retain the explicit motive, the inner matches becoming implicit.

Note that while this kind of match provides a way to explicitly refine the *output* type when matching against a non-variable term, unlike a variable match, it does not do anything to the types of other variables in the context.  If you want their types to also be refined in the branches when doing an explicitly dependent match, you have to use the `convoy pattern <http://adam.chlipala.net/cpdt/html/MoreDep.html>`_ as in Coq.


Matches in terms and case trees
-------------------------------

The other case tree constructs we have discussed, such as abstraction and tuples, can also occur in arbitrary locations in a term.  The same is true for matches, but the behavior of such matches is somewhat subtle.

If ``match`` were an ordinary kind of term syntax, Narya would have to be able to check whether two ``match`` expressions are equal.  Matches don't satisfy η-conversion, so such an equality-check would have to descend into the branch bodies, and this would require *normalizing* those bodies.  Now suppose a function were defined recursively using a match outside its case tree; then it would evaluate to a match expression even if its argument is not a constructor, and it would appear itself in one of the branches of that match expression; thus, this would lead to an infinite regress of normalization.  This is probably not an impossible problem to solve (e.g. Coq has fixpoint terms and match terms and manages to check equality), but it would be complicated and does not seem worth the trouble.

Narya's solution is similar to that of Agda: matches outside case trees are *generative*.  (Note that matches inside case trees are also generative in the sense that all constants defined by case trees are generative.)  Each textual occurrence of a match is, in effect, lifted to a top-level definition (actually, a metavariable) which contains the match *inside* its case tree, and therefore doesn't reduce to anything unless the discriminee is a constructor.  In particular, therefore, two such matches, even if they look identical, generate distinct lifted top-level definitions and thus are not definitionally equal (until their discriminees become constructors and they reduce to corresponding branches).  This sort of lifting allows us to say that, technically, ``match`` is *only* allowed in case trees, and any occurrences outside of case trees are silently elaborated into case trees.

Narya attempts to be "smart" about such lifting in a couple of ways.  Firstly (and perhaps obviously), once a ``match`` is encountered in a term and lifted to the case tree of a top-level definition, that case tree continues as usual into the branches of the match, including all operations that are valid in case trees such as abstractions, tuples, and other matches, until it reaches a leaf that can't be a case tree node.  Thus, reduction of such a match is blocked not only on its own discriminee, but on those of all directly subsequent matches appearing in its branches.

Secondly, if a ``match`` appears directly as the value of a ``let`` binding (or nested only inside other case tree constructs), then the *entire* value of the let-binding is lifted to top-level as a case tree definition, and then bound locally to the ``let`` variable.  Thus, ``let`` can be treated like a local version of ``def``, defining a function locally by a case tree that doesn't reduce until applied to enough arguments, field projections, and constructors.  Unlike a ``def``, however, the *default* behavior of ``let`` is to interpret its argument as a term rather than a case tree: it only interprets its argument as a case tree if there are case-tree-only constructs like ``match`` that *would* be included in it under such an interpretation.  Thus, for instance,

.. code-block:: none

   def point : ℕ × ℕ 
     ≔ let p : ℕ × ℕ ≔ (1,2) in 
       p
        
   echo point

will print ``(1,2)``, in contrast to how ``def point : ℕ × ℕ ≔ (1,2)`` would be printed simply as `point` since the tuple would be part of the case tree (unless the product type ``×`` is transparent or translucent).  But, for instance, if we define a function locally to pass to some other functional, that local function can be defined by matching:

.. code-block:: none

   def sq (f : ℕ → ℕ) : ℕ → ℕ ≔ x ↦ f (f x)
   
   def sqdec1 (x : ℕ) : ℕ ≔
     let dec : ℕ → ℕ ≔ y ↦ match y [ zero. ↦ zero. | suc. n ↦ n ] in
     sq dec x

Such local functions are very like Agda's ``where`` clauses.  They cannot yet be defined with parameter syntax (e.g. "``let dec (y:ℕ) : ℕ ≔``"), but we can use a pattern-matching lambda for a one-variable function:

.. code-block:: none

   def sqdec2 (x : ℕ) : ℕ ≔
     let dec : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ n ] in
     sq dec x

Of course, we can also just pass the pattern-matching lambda directly as a term on its own:

.. code-block:: none

   def sqdec3 ≔ sq [ zero. ↦ zero. | suc. n ↦ n ]

However, a let-bound local function can use a ``let rec`` instead to define a local recursive function, which is not possible with a pattern-matching lambda:

.. code-block:: none

   def sqdbl (x : ℕ) : ℕ ≔
     let rec dbl : ℕ → ℕ ≔ y ↦ match y [ zero. ↦ zero. | suc. n ↦ suc. (suc. (dbl n)) ] in
     sq dbl x

In fact, ``let rec`` is *always* treated generatively and lifted to top-level like an ordinary ``let`` that contains a ``match``.  Indeed, in the absence of something like a "fixpoint" operator there is no other possibility, as there is no term syntax for it to evaluate to.

Currently, such local case trees are not printed very comprehensibly if they "escape" from their site of definition.  For instance:

.. code-block:: none

   axiom z : ℕ
   
   echo sqdec2 z

prints something like ``_let.0.dec{…} (_let.0.dec{…} z)``, where the number is a metavariable counter.  The name ``_let.0.dec`` is not a valid user-defined identifier since it begins with an underscore, and so this notation is not re-parseable; but it indicates that there is some locally defined function, which was called ``dec`` where it was defined but is not in scope any more, and is being applied twice to the argument ``z``.  The notation ``{…}`` is like that used for a hole, indicating that this local function might also have an un-notated substitution applied to the context in which it was defined.  As noted above, like any other global constant defined by a case tree, ``_let.0.dec`` does not evaluate at all unless it reaches a leaf of its case tree; thus ``_let.0.dec{…} (_let.0.dec{…} z)`` does not reduce further since ``z`` is not a constructor.  (But ``sqdec (suc. z)`` will, of course, reduce once to ``_let.0.dec{…} z``.)

As noted above, such local case trees are generative: textually identical definitions given in two different places will produce unequal values.

.. code-block:: none

   def dec1_is_dec2 ≔ 
     let dec : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ n ] in
     let dec1 ≔ dec in
     let dec : ℕ → ℕ ≔ [ zero. ↦ zero. | suc. n ↦ n ] in
     let dec2 ≔ dec in
     Jd (ℕ → ℕ) dec1 dec2

   def fails : dec1_is_dec2 ≔ rfl.
   
      ￫ error[E1003]
    1 | def fails : dec1_is_dec2 ≔ rfl.
      ^ index
          _let.1.dec{…}
        of constructor application doesn't match the corresponding index
          _let.2.dec{…}
        of datatype instance

Note that both local functions are called ``_let.N.dec`` based on their name when defined, but their metavariable counters are different, and they are unequal.

A match not occuring inside any ``let`` value doesn't even have a user-assigned name like ``dec``, so it is printed only with a number.  For instance, ``echo sqdec3`` from above will print something like ``sq (H ↦ _match.3{…})``.  Note that the dependence of the match on the variable (which Narya named ``H``) is not even indicated (it is hidden in the context substitution ``{…}``).  However, the advantage of matches of this sort is that, unlike the value of a let-bound variable, they can check rather than synthesize.

The printing of local case trees will hopefully be improved somewhat in future, but there is a limit to how much improvement is possible.  Moreover, overuse of local case trees can make it difficult to prove theorems about a function: facts one may need about its components cannot easily be separated out into lemmas since the pieces cannot easily be referred to.  Thus, while this sort of code can be convenient for programming, and in simple cases (such as ``match e [ ]`` to fill any checking context, given any ``e:⊥``), it is often better eschewed in favor of additional explicit global helper functions.  For this reason, Narya currently emits a hint whenever it detects a "bare" case-tree-only construct and interprets it in this way.

