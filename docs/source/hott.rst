Higher Observational Type Theory
================================

Although Narya can be used for various different higher type theories, its primary *raison d'être* is Higher Observational Type Theory (HOTT), a computational version of Homotopy Type Theory (HoTT) in which the identity types are defined "observationally".  HOTT can be encoded inside parametricity, and there is a native HOTT mode in development.

Native HOTT mode
----------------

The native HOTT mode is activated by the command-line flag ``-hott``.  This conflicts with any other flags that modify the direction of parametricity: it must be binary with letter ``e`` and degeneracy names ``Id`` and ``refl``.  (In the future, we plan to allow multiple directions of higher-dimensionality, so that internal parametricity can coexist with HOTT in a different direction.)  In particular, when working in HOTT mode you may want to start all your source files with the line

.. code-block:: none

   {` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

Transport and lifting
^^^^^^^^^^^^^^^^^^^^^

In HOTT mode, types can be treated also like codata, with four one-dimensional higher fields:

- ``trr``: transport left to right
- ``liftr``: path-lifting left to right
- ``trl``: transport right to left
- ``liftl``: path-lifting right to left

Saying that these are one-dimensional higher fields means that they can only be projected out of a higher-dimensional type, and more generally that each of them has *n* instances when applied to an *n*-dimensional type.  The simplest and most common case is a one-dimensional type, that is an equality in the universe.  In this case, the types of these fields are as follows: given ``A₂ : Id Type A₀ A₁``, we have

.. code-block:: none

   A₂ .trr : A₀ → A₁
   A₂ .liftr : (x₀ : A₀) → A₂ x₀ (A₂ .trr x₀)
   A₂ .trl : A₁ → A₀
   A₂ .liftr : (x₁ : A₁) → A₂ (A₂ .trl x₁) x₁

More verbosely, these fields can also be denoted ``.trr.1`` and so on.  For a higher-dimensional type, the fields are numbered by dimension and yield "uniform" versions of these operations acting from one face to the opposite face.  For instance, given ``A₂₂ : Type⁽ᵉᵉ⁾ A₀₂ A₁₂ A₂₀ A₂₁``:

- If ``a₀₂ : A₀₂ a₀₀ a₀₁``, then ``A₂₂ .trr.1 a₀₂ : A₁₂ (A₂₀ .trr a₀₀) (A₂₁ .trr a₀₁)``.
- If ``a₂₀ : A₂₀ a₀₀ a₁₀``, then ``A₂₂ .trr.2 a₂₀ : A₂₁ (A₀₂ .trr a₀₀) (A₁₂ .trr a₁₀)``.

and so on.  In addition, by instantiating ``A₂₂`` we get a one-dimensional type, which has its own operations.  For instance, given ``a₀₂`` and ``a₂₀`` as above, and also ``a₁₂ : A₁₂ a₁₀ a₁₁``, we have ``A₂₂ a₀₂ a₁₂ .trr a₂₀ : A₂₁ a₀₁ a₁₁``.  As in cubical type theories, when combined with symmetry these "box-filling operations" suffice to construct all the higher groupoid structure of homotopy type theory, including the Martin-Löf eliminatior ``J`` for ``Id`` (with typal computation rule).  A proof of the latter can be found in `test/black/hott.t/J.ny <https://github.com/gwaithimirdain/narya/tree/master/test/black/hott.t/J.ny>`_.

In theory, these operations should all compute based on the type ``A₂`` or ``A₂₂``, making HOTT a fully computational theory.  However, this is not yet fully implemented; currently they compute only for:

- Function types
- Zero-dimensional record types and codatatypes without higher fields


Glue types and univalence
^^^^^^^^^^^^^^^^^^^^^^^^^

The final change in HOTT mode is that gel types are replaced by glue types.  Specifically, it is no longer possible to define elements of ``Id Type A B`` as explicit record or codata types.  Instead, there is a built-in constant ``glue`` with the following type:

.. code-block:: none

   glue : (A B : Type) (R : A → B → Type) (Rb : isBisim A B R) → Id Type A B

That is, ``glue`` is like the ``Gel`` that under parametricity can be defined as a higher-dimensional record type, but it also requires the given correspondence ``R`` to be a *bisimulation* of types.  Here ``isBisim`` is another built-in constant defined as follows:

.. code-block:: none

   def isBisim (A B : Type) (R : A → B → Type) : Type ≔ codata [
   | x .trr : A → B
   | x .liftr : (a : A) → R a (x .trr a)
   | x .trl : B → A
   | x .liftl : (b : B) → R (x .trl b) b
   | x .id.e
     : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1) (r1 : R.1 a1 b1)
       → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a0 a1 a2 b0 b1 b2 r0 r1) ]

Note that it has four ordinary fields that are non-recursive, and one higher field that is recursive.  It is possible to prove that any equivalence gives rise to a bisimulation, and thereby deduce univalence; this can be found in `test/black/hott.t/univalence.ny <https://github.com/gwaithimirdain/narya/tree/master/test/black/hott.t/univalence.ny>`_.  Eventually, the fields of ``isBisim`` will be used to compute the built-in operations ``trr`` on ``glue`` types, making univalence computational.

The syntax of ``glue`` and ``isBisim`` is provisional and may change in the future.


Equational reasoning
--------------------

In ``-hott`` mode, elements of ``Id`` are equalities, hence in particular are not just reflexive but also symmetric and transitive.  There is a temporary convenient syntax for equational reasoning with such equalities, which is exemplified as follows:

.. code-block:: none

   def eqreas (A : Type) (x y z w : A) (p : Id A x y) (q : Id A y z) (r : Id A w z)
     : Id A x w ≔ calc
     x
     = y
         by p
     = z
         by q
     = w
         by r ∎

Note that the supplied reason for each equality can be applied either forwards or backwards, without the user needing to notate which.  However, all congruences must be applied explicitly (e.g. with ``refl``).  If two subsequent terms are definitionally equal, the ``by`` clause can be omitted; this allows notating applications of definitional equality in a more readable way.


HOTT inside parametricity
-------------------------

HOTT can also be encoded in binary observational parametricity by defining a higher coinductive fibrancy predicate:

.. code-block:: none

   def isFibrant (A : Type) : Type ≔ codata [
   | x .trr.e : A.0 → A.1
   | x .trl.e : A.1 → A.0
   | x .liftr.e : (a₀ : A.0) → A.2 a₀ (x.2 .trr.1 a₀)
   | x .liftl.e : (a₁ : A.1) → A.2 (x.2 .trl.1 a₁) a₁
   | x .id.e : (a₀ : A.0) (a₁ : A.1) → isFibrant (A.2 a₀ a₁)
   ]

All five methods are 1-dimensional, so their types are defined in a higher-dimensional context consisting of

.. code-block:: none

   A.0 : Type
   A.1 : Type
   A.2 : Id Type A.0 A.1
   x.0 : isFibrant A.0
   x.1 : isFibrant A.1
   x.2 : refl isFibrant A.0 A.1 A.2 x.0 x.1

In other words, the behavior of fibrancy only becomes visible once we have not just one fibrant type, but an equality between fibrant types (including their witnesses of fibrancy).  Given this, the fields ``trr`` and ``trl`` say that we can transport elements back and forth across such an equality, while the fields ``liftr`` and ``liftl`` give "path lifting" operations that "equate" each point to its transported version, heterogeneously along the family ``A``.  Finally, the last field ``id`` says corecursively that the (heterogeneous) identity types of a fibrant type are again fibrant.

The file `test/black/hct-hott.t/fibrant_types.ny <https://github.com/gwaithimirdain/narya/tree/master/test/black/hct-hott.t/fibrant_types.ny>`_ contains proofs that this notion of fibrancy is preserved by most of the standard type constructors (the exceptions being indexed inductive types, which require "fibrant replacement", and the universe, which should be fibrant but this may not be provable internally).  These proofs, in turn, translate into the *definitions* of how the transport and lifting operations should compute on canonical types in the native HOTT mode (although they have to be generalized from, say, W-types to arbitrary inductive types, and so on).
