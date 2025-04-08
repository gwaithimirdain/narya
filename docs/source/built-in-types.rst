Built-in types
==============

The universe
------------

Currently there is only one universe ``Type`` that contains all types, including itself, making the type theory inconsistent.  In the future it is planned to incorporate universe levels using `mugen <https://github.com/redPRL/mugen>`_.


Functions and function-types
----------------------------

Apart from the universe, the only predefined type is a dependent function-type, written ``(x:A) → B x`` as in NuPRL and Agda.  As usual, if ``B`` does not depend on ``x`` one can simplify this to ``A → B``, and iterated function-types can be combined, including combining multiple variables with the same type, as in ``(x y : A) (z : B x y) → C x y z``.  Also as usual, this notation is right-associative, so ``A → B → C`` means ``A → (B → C)``.  The unicode → appearing here is interchangeable with the ASCII ``->``.

Again as usual, functions are applied by juxtaposition; if ``f : (x:A) → B x`` and ``a : A`` then ``f a : B a``.  And this is left-associative, so if ``f : A → B → C`` then ``f a b : C``.

Functions are introduced by abstraction, which in Narya is written (somewhat unusually) as ``x ↦ M``, or ``x y z ↦ M`` to abstract multiple variables at once.  The unicode ↦ is interchangeable with the ASCII ``|->``.

The variable in a function-type or an abstraction can be replaced by an underscore ``_``, indicating that that variable is not used and thus needs no name.  For types this is equivalent to a non-dependent function-type: ``(_ : A) → B`` means the same as ``A → B``.  For abstractions, ``_ ↦ M`` defines a constant function, whose value doesn't depend on its input.

In addition, there is a built-in constant called ``Π`` that represents dependent function-types.  The type of ``Π`` is ``(X : Type) → (X → Type) → Type``, and ``Π A B`` reduces to ``(x : A) → B x``.  In other words, it behaves as if defined by

.. code-block:: none

   def Π (A : Type) (B : A → Type) : Type ≔ (x : A) → B x

This is mainly useful for writing and printing higher-dimensional function-types (see :ref:`Parametric Observational Type Theory`).

