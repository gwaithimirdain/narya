Typechecking details
====================

Bidirectionality
----------------

Narya's typechecker is bidirectional.  This means that some terms *synthesize* a type, and hence can be used even in a place where the "expected" type of a term is not known, whereas other terms *check* against a type, and hence can only be used where there is an "expected" type for them to check against.  Of the terms we have mentioned so far:

- Function application ``M N`` synthesizes, by first requiring ``M`` to synthesize a function-type ``(x:A) → B``, then checking ``N`` against the input type ``A``, and finally synthesizing the corresponding output ``B[N/x]``.

- Function abstraction ``x ↦ M`` checks against a function-type ``(x:A) → B`` by checking ``M`` against ``B`` in a context extended by a variable ``x:A``.  In particular, this means that the same abstraction term can mean different things depending on what type it is checked against.  For instance, ``x ↦ x`` checks against *any* endo-function type ``A → A``.  (Speaking semantically, however, we do not regard this as "one term having multiple types"; rather we consider that the typechecker is elaborating the ambiguous notation ``x ↦ x`` using contextual information to produce a distinct identity term in each endo-function type.)

- Type-forming operators such as ``Type`` and ``(x:A) → B`` synthesize, after requiring their inputs to synthesize.  This might be modified later after universe levels are introduced.

- Variables and constants synthesize their declared types.


Ascription
----------

If you want to use a checking term in a synthesizing position, you have to *ascribe* it to a particular type by writing ``M : A`` (or ``M:A`` by the lexer rules discussed above, assuming ``M`` doesn't end, or ``A`` start, with a special ASCII character notation).  This *checks* ``M`` against the supplied type ``A``, and then itself *synthesizes* that type.  For example, you cannot directly apply an abstraction to an argument to create a redex as in ``(x ↦ M) N``, since the abstraction only checks whereas a function being applied must synthesize, but you can if you ascribe it as in ``((x ↦ M) : A → B) N``.  In general, ascription tends only to be needed when explicitly writing a redex or something similar.

The ascription notation has tightness −ω, and is non-associative, so that ``M : N : P`` is a parse error.  However, the right-associativity of ``↦`` and the fact that they share the same tightness means that ``x ↦ M : A`` is parsed as ``x ↦ (M : A)``, hence the placement of parentheses in the above example redex.

*Side note:* The coexistence of type ascription and NuPRL/Agda-style dependent function-types leads to a potential ambiguity: ``(x : A) → B`` could be a dependent function type, but it could also be a *non-dependent* function type whose domain ``x`` is ascribed to type ``A`` (which would therefore have to be a type universe).  Narya resolves this in favor of the dependent function type, which is nearly always what is intended.  If you really mean the other you can write it as ``((x : A)) → B`` or ``((x) : A) → B``; but I can't imagine why you would need to do this, since the only possible ambiguity is when ``x`` is a variable (or a list of variables), and variables and constants (and application spines of such) always synthesize their type anyway and thus don't need to be ascribed.


Let-binding
-----------

Writing ``let x ≔ M in N`` binds the local variable ``x`` to the value ``M`` while typechecking and evaluating ``N``.  The unicode ≔ is interchangeable with the ASCII ``:=``.  Computationally, ``let x ≔ M in N`` is equivalent to ``(x ↦ N) M``, but it also binds ``x`` to the value ``M`` while typechecking ``N``, which in a dependent type theory is stronger.

The term ``M`` is required to synthesize.  Thus ``let x ≔ M : A in N`` is a common idiom, and can be written alternatively as ``let x : A ≔ M in N``.  The body ``N`` can either check or synthesize, and the let-binding as a whole inherits this from it: if ``N`` synthesizes a type then the let-binding synthesizes the same type, while if ``N`` checks then the let-binding checks against a type that is passed on to ``N`` to check against.  The let-binding notation is right-associative with tightness −ω.

An ordinary let-binding is not recursive: the variable ``x`` cannot appear in the term ``M``.  This is intentional and enables a common idiom where ``x`` shadows a previously existing variable of the same name in ``N``, while the *previous* variable of that name can appear in ``M``, thereby creating the illusion that the value of that variable has been "changed".  For instance, ``let x ≔ x + 1 in`` has the appearance of incrementing the value of ``x``.

However, it is possible to define a recursive let-binding by writing ``let rec`` instead of ``let``.  (Note that ``let`` and ``rec`` are two keywords separated by a space.)  In this case, the variable ``x`` *can* appear in ``M``, and of course shadows any previously defined variable of the same name in ``M`` as well as in ``N``.  In a recursive let-binding the type of ``M`` must be given explicitly (as with a top-level ``def`` which can also be recursive): the only valid syntax is ``let rec x : A ≔ M in N``.  (Recursive let-bindings are also treated "generatively", like let-bindings that include matches or comatches; see below.)


Eta-conversion and case trees
-----------------------------

Functions satisfy undirected η-conversion (in addition to the obvious directed β-reduction).  That is, while neither of ``x ↦ f x`` or ``f`` *simplifies* to the other, they are considered equal for the purposes of typechecking (they are "convertible").  The way this works is that the equality-checking algorithm is type-sensitive, and when comparing two terms at a function type it first applies them to a fresh variable, and ``(x ↦ f x) y`` then reduces to ``f y``.

In addition, constants defined as functions do not reduce until they are applied to all of their arguments, including both arguments declared as parameters (before the colon) and those not so declared.  For instance, if we define addition of Church numerals as

.. code-block:: none
   
   def cplus (A:Type) (m n : (A → A) → (A → A)) : (A → A) → (A → A) ≔
   f x ↦ m f (n f x)

then ``cplus A (f x ↦ f x) (f x ↦ f x)`` (i.e. "1 + 1") doesn't reduce to ``(f x ↦ f (f x))`` because it is not fully applied, whereas ``cplus A (f x ↦ f x) (f x ↦ f x) f x`` does reduce to ``f (f x)``.  However, ``cplus A (f x ↦ f x) (f x ↦ f x)`` is still *convertible* with ``(f x ↦ f (f x))`` because equality-checking does η-conversion.  If you want to display the body of a constant defined as a function, you must manually η-expand it, which means it has to be ascribed as well:

.. code-block:: none

   echo (A f x ↦ cplus A (f x ↦ f x) (f x ↦ f x) f x)
      : (A:Type) → (A → A) → (A → A)
  
   A f x ↦ f (f x)
      : (A : Type) → (A → A) → A → A

If there is significant demand for displaying function bodies, we may add an option to ask for η-expansion.

More generally, the definition of a constant is not just a term, but something called a *case tree*, which can contain internal nodes of different sorts and ends in ordinary terms at its leaves.  Evaluation of such a constant, applied to arguments, does not reduce to anything unless the arguments are sufficient and sufficiently informative for the evaluation to reach a leaf.  In fact *every* defined constant in Narya is actually defined to equal a case tree, even if it consists only of a single leaf.

So far, the only kinds of case tree node we have seen are abstractions and let-bindings.  The requirement for abstractions in a case tree to reduce is just that the function receives enough arguments to β-reduce all the abstractions, and let-bindings in a case tree reduce if their body does.  Thus, in particular, an abstraction directly inside a let-binding, such as that over ``y`` above, must also receive an argument before the definition reduces.  Other kinds of case tree nodes, with their own reduction rules, include tuples, matches, and comatches, discussed below.

Since abstractions and let-bindings can also occur at arbitrary positions in a term, there is some potential ambiguity in a definition containing these: are they part of the case tree, or part of a unique body term?  The rule to resolve this is that the case tree includes *as much as possible*.  Once another kind of term is encountered that cannot be a case tree node, then that term and all its sub-terms (including any abstractions or let-bindings) are part of the leaf.  Thus, for instance, in

.. code-block:: none
   
   def foo : A → B → C ≔ 
      x ↦ 
      let y ≔ M in
      y ↦
      f (z ↦ N)

the abstractions over ``x`` and ``y`` are part of the case tree, as is the let-binding, but the abstraction ``z ↦ N`` is not.  Thus, ``foo`` and ``foo a`` will not reduce, but ``foo a b`` will reduce.  This behavior is usually what you want, but if you really want to define a constant that reduces to an abstraction before it receives an argument you can wrap it in a no-op redex:

.. code-block:: none
   
   def id (A:Type) : A → A
        ≔ ((f ↦ f) : (A → A) → (A → A)) (x ↦ x)

Since a function application cannot be part of a case tree, it goes into the body term, including the abstraction over ``f``; thus ``id A`` will reduce to ``x ↦ x``.  Unfortunately the identity function has to be ascribed, as always whenever you write an explicit redex.  A slightly less verbose way to achieve this is to let-bind the abstraction to a variable and then return the variable, since let-bindings are fully evaluated before being assigned to a variable:

.. code-block:: none
   
   def id (A:Type) : A → A
        ≔ let id' : A → A ≔ (x ↦ x) in id'

However, the type ``A → A`` still has to be written again, since a let-binding must synthesize.  If there is significant demand for it, we may implement a less kludgy way to force transitioning from case tree nodes to a leaf.
