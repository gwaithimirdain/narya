Codatatypes and comatching
==========================

A *codatatype* is superficially similar to a record type: it has a list of fields (which in this case we sometimes call *methods*), each with a type, which are projected out (or "called") using the same syntax ``x .method``.  The primary differences are:

1. Codatatypes can be (co)recursive: the output type of each method can involve the codatatype itself.  (Such occurrences ought to be strictly positive, but currently there is no check for that.  In fact, there is not yet even a check that rules out recursion in record types, but there will be.)
2. Codatatypes do not satisfy η-conversion (this being undecidable in the recursive case).
3. Elements of codatatypes are defined by *comatches*, which are like tuples but can be recursive, use a syntax more akin to matches, and are restricted to case trees.


Defining codatatypes
--------------------

Here is a corecursive definition of the codatatype of infinite streams:

.. code-block:: none

   def Stream (A:Type) : Type ≔ codata [
   | x .head : A
   | x .tail : Stream A
   ]

That is, we use brackets and bars instead of parentheses and commas.  Moreover, instead of writing field names like variables as in a record type, we write them as method calls *applied to a variable*.  This variable is then bound in the body to belong to the codatatype, and the values of previous fields are accessed through it.  For instance, a codata version of Σ-types would be written

.. code-block:: none

   def codata-Σ (A : Type) (B : A → Type) : Type ≔ codata [
   | x .fst : A
   | x .snd : B (x .fst)
   ]

It is often helpful to think of a codatatype as akin to an *interface* in an object-oriented programming language, in which case the variable ``x`` is like the ``this`` or ``self`` pointer by which an object refers to itself.  Of course an interface in a simply-typed language does not need a self-pointer to specify the *types* of its methods, but in a dependently typed language it does.  In higher-dimensional type theories, the presence of this variable can be used in other ways than simply accessing previously declared methods, such as in the definition of semi-simplicial types using :ref:`Displayed coinductive types`.


Copattern matching
------------------

Elements of coinductive types are introduced by comatches, which are like tuples except for the syntax and the fact that they can be (co)recursive:

.. code-block:: none

   def Fibonacci (a b : ℕ) : Stream ℕ ≔ [
   | .head ↦ a
   | .tail ↦ Fibonacci b (ℕ.plus a b)
   ]

In addition, unlike tuples, comatches are a part of case trees but not of ordinary terms.  Thus, they never evaluate to anything until a method is called.  This is essential to ensure termination in the presence of corecursion; otherwise ``Fibonacci 1 1`` would spin forever computing the entire infinite sequence.  (It is also why codatatypes do not have `η-conversion <http://strictlypositive.org/Ripley.pdf>`_.)  It is often helpful to think of a constant defined by comatching as an (`immutable <https://dev.realworldocaml.org/objects.html>`_) *object* implementing an interface, with the parameters of that constant being its "private member variables".

(As a bit of syntactic trivia, note that ``[]`` is ambiguous: it could denote either a pattern-matching lambda on a datatype with no constructors, or a copattern-match into a codatatype with no methods.  Fortunately, since both possibilities are checking rather than synthesizing, and function-types and codatatypes are disjoint, the ambiguity is resolved by bidirectional typechecking.)

