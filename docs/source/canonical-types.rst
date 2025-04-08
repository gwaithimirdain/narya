Canonical types defined by case trees
=====================================

By a *canonical type* we mean a universe, function-type, record type, datatype, or codatatype, of which the first two are built in and the latter three are all user-defined.  So far, all our definitions of new canonical types (record types, datatypes, and codatatypes) may have been abstracted over parameters, but otherwise the keyword ``sig`` or ``data`` has occurred immediately after the ≔.

However, in fact a canonical type declaration can appear anywhere in a case tree!  For example, here is another definition of length-indexed lists, which we call "covectors".  Now instead of the length being an index, it is a *parameter* over which we recurse:

.. code-block:: none

   def Covec (A:Type) (n:ℕ) : Type ≔ match n [
   | zero. ↦ sig ()
   | suc. n ↦ sig (
     car : A,
     cdr : Covec A n )]

Thus, ``Covec A 0`` is a unit type, ``Covec A 1`` is isomorphic to ``A`` (definitionally! since record types have η-conversion), ``Covec A 2`` is isomorphic to ``A × A``, and so on.

This is very similar to, but subtly different from, the following definition that could be given in Coq or Agda:

.. code-block:: none

   def Covec' (A:Type) (n:ℕ) : Type ≔ match n [
   | zero. ↦ ⊤
   | suc. n ↦ A × Covec' A n]

The two are definitionally isomorphic at any concrete numeral ``n``, and equivalent in general.  The difference is that ``Covec' A n`` reduces when ``n`` is a constructor, while ``Covec A n`` is already a canonical type no matter what ``n`` is; it's just that when ``n`` is a constructor we know how it *behaves*.  For instance, ``Covec' A 2`` reduces to ``A × (A × ⊤)``, whereas ``Covec A 2`` does not reduce but we can still typecheck ``(a, (b, ()))`` at it.  This sort of "recursively defined canonical type" helps maintain information about the meaning of a type, just like using a custom record type rather than a nested Σ-type; eventually we hope it will be helpful for unification and typeclass inference.

As another example, once we have an identity type ``Id`` (which could be ``Jd``, or an observational identity type) we can define the homotopy-theoretic tower of truncation levels:

.. code-block:: none

   def trunc_index : Type ≔ data [ minustwo. | suc. (_ : trunc_index) ]
   
   def IsTrunc (n:ℕ) (A:Type) : Type ≔ match n [
   | minustwo. ↦ sig ( center : A, contr : (x:A) → Id A center x )
   | suc. n ↦ sig ( trunc_id : (x y : A) → IsTrunc n (Id A x y) )]

Definitions of datatypes by recursion can sometimes be used in place of indexed datatypes.  In particular, this can sometimes be a good way of getting around Narya's lack of unification for indices in pattern-matching.  For example, if we define the standard finite types as an indexed datatype:

.. code-block:: none

   def Fin : ℕ → Type ≔ data [
   | zero. : (n : ℕ) → Fin (suc. n)
   | suc.  : (n : ℕ) → Fin n → Fin (suc. n)]

then matching against an element of ``Fin n`` will only refine the goal and context if the index ``n`` is a free variable.  This means we need technical circumlocutions even to prove that, for instance, ``Fin zero.`` is empty.  However, we can instead define ``Fin`` recursively:

.. code-block:: none

   def Fin : ℕ → Type ≔ [
   | zero.  ↦ data [ ]
   | suc. n ↦ data [ zero. | suc. (_ : Fin n) ]]

Now ``Fin zero.``, while it is canonical and doesn't reduce to anything, can also be proven to be empty by direct matching:

.. code-block:: none

   def Fin.zero_empty : Fin zero. → ⊥ ≔ [ ]

Similarly, we can do a deep match against particular finite types:

.. code-block:: none

   def count_Bool2 : Fin 4 → Bool × Bool ≔ [
   | zero. ↦ (true., true.)
   | suc. zero. ↦ (true., false.)
   | suc. (suc. zero.) ↦ (false., true.)
   | suc. (suc. (suc. zero.)) ↦ (false., false.)]

Here we also see another advantage of the recursive approach: the index ``n`` is not an argument of the constructors, so the syntax is much simpler.  In the inductive approach we would have to write ``suc. 3 (suc. 2 (zero. 1))`` for "2" in ``Fin 4``, and there are not yet any implicit arguments or unification.

Like ``match`` and ``comatch``, the constructs ``sig``, ``data``, and ``codata`` can technically only occur in case trees, so if they appear outside a top-level case tree or ``let`` binding they are automatically lifted to a top-level case tree.  Also like ``match`` and ``comatch``, they are generative, and when they occur outside a top-level case tree they are not printed comprehensibly.  For example:

.. code-block:: none

   def foo : ⊤ ≔
     let A : Type ≔ sig () in
     let B : Type ≔ sig () in
     let f : A → B ≔ x ↦ x in
     ()
   
    ￫ error[E0401]
    4 |   let f : A → B ≔ x ↦ x in
      ^ term synthesized type
          _let.0.A
        but is being checked against type
          _let.1.B

Thus, it is probably ill-advised to use such "on-the-fly" definitions of canonical types very much.  However, it may sometimes be convenient to, for example, pass a custom type like ``data [ red. | green. | blue. ]`` directly as an argument to some other function.  Types defined directly on the fly like this cannot be recursive, so in practice their usefulness is mostly restricted to record types and enumerated types (which could, in theory, also be printed more comprehensibly, and even treated non-generatively).  However, local recursive types can be defined with ``let rec``, e.g. ``let rec ℕ : Type ≔ data [ zero. | suc. (_:ℕ) ] in ...``.
