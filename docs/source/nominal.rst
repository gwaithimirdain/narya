Nominal type theory
===================

Nullary parametricity (arity 0) is a form of nominal type theory: its intended model is the "constructive Schanuel topos" over a base, consisting of presheaves on the category of finite sets and monomorphisms.  From the nominal perspective, an *n*-dimensional term is regarded as depending on *n* variables or "names", with ``rel`` acting as weakening and ``sym`` permuting the names.  Thus we generally combine ``-arity 0`` with ``-direction w,wk`` for weakening.

It is curious that observational nullary parametricity gives us something akin to a "nominal" type theory without any explicit reference to *names* at all.  Rather, the *dimension* of an object indicates how many "names" it depends on, and permutation of those names is accomplished explicitly by ``sym`` and other permutations.  For example, the fresh quantifier ``И`` of nominal type theory can be defined using :ref:`Higher coinductive types`:

.. code-block:: none

   def И (A : Type) : Type ≔ codata [
   | x .subst.w : A .
   ]

Intuitively, ``И A`` is the type of terms of ``A`` that "bind" a dependence on one additional fresh name.  Accordingly, if we have an element ``a : wk (И A) .`` in the context of an *additional* name, then ``a .subst : wk A .`` is an element of ``A`` depending only on this same additional name, in which that name has been "substituted" for the fresh name bound in ``a``.  And if we have ``b : (И A)⁽ʷʷ⁾ . .`` depending on two additional names, we have both ``b .subst.1 : A⁽ʷʷ⁾ . .`` and ``b .subst.2 : A⁽ʷʷ⁾ . .``, which respectively substitute each of the additional names for the fresh one bound in ``b``.
