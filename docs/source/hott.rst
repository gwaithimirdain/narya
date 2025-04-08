Higher Observational Type Theory
================================

Although Narya can be used for various different higher type theories, its *raison d'être* is Higher Observational Type Theory (HOTT), a version of Homotopy Type Theory (HoTT) in which the identity types are defined "observationally".  HOTT is not yet implemented natively, but can be encoded in binary observational parametricity by defining a higher coinductive fibrancy predicate:

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

Taken together, this suffices to construct all the higher groupoid structure in homotopy type theory.  Some examples can be found in `test/black/hott.t <https://github.com/gwaithimirdain/narya/tree/master/test/black/hott.t>`_, including the proof that standard types inherit fibrancy, and that univalence holds.
