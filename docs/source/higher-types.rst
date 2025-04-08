Higher datatypes and codatatypes
================================

There are many possible kinds of datatypes and codatatypes that make use of higher-dimensional structure.

Higher inductive types
----------------------

These are not implemented yet.


Higher coinductive types
------------------------

By a "higher coinductive type" we mean a codatatype in which the *input* of a method is a higher-dimensional version of itself, dually to how a "higher inductive type" has constructors whose *output* is a higher-dimensional version of itself.  The simplest example of a higher coinductive type is the "amazing right adjoint" of the identity type.  Applied to a concrete type like ``ℕ``, this has the Narya syntax:

.. code-block:: none

   def √ℕ : Type ≔ codata [
   | x .root.e : ℕ
   ]

Recall that a field name cannot contain internal periods.  This may appear to be an exception, but in fact the real name of the field here is actually just ``root``.  The suffix ``e`` is a marker indicating that it is a 1-dimensional field (when ``e`` is the direction letter, as in the default configuration).  The argument ``x`` of this field is therefore a 1-dimensional "cube variable", as we can see by leaving a hole instead:

.. code-block:: none

   def √ℕ : Type ≔ codata [
   | x .root.e : ?
   ]
   
    ￫ info[I0100]
    ￮ hole ?0 generated:
      
      x.0 : √ℕ
      x.1 : √ℕ
      x.2 : refl √ℕ x.0 x.1
      ----------------------------------------------------------------------
      Type

Unsurprisingly, therefore, the field ``root`` can only be projected out of a higher-dimensional inhabitant of ``√ℕ``.  If we try to project it out of an ordinary element we get an error:

.. code-block:: none

   axiom x : √ℕ
   echo x .root
   
     ￫ error[E0801]
    1 | x .root
      ^ codata type √A has no field named root

The syntax for using a higher field is different from the syntax for defining it, however.  In the simplest case, when projecting from a 1-dimensional element, we replace the suffix ``e`` by ``1``:

.. code-block:: none

   axiom x : √ℕ
   axiom y : √ℕ
   axiom z : Id √ℕ x y
   echo z .root.1

   z .root.1
     : ℕ

Just as the higher-dimensional versions of an ordinary codatatype inherit fields of the same name, the same is true for higher codatatypes, but with a twist.  Namely, a 1-dimensional field like ``root`` induces *two* fields that can be projected out of a 2-dimensional version of ``√ℕ``, corresponding to the two directions of a square, and these are distinguished by different numerical suffixes.  For example, if we have

.. code-block:: none

   x22 : √ℕ⁽ᵉᵉ⁾ x00 x01 x02 x10 x11 x12 x20 x21

with ``x00`` through ``x21`` of appropriate types, then the two projectable fields of ``x22`` and their types are

.. code-block:: none

   x22 .root.1 : refl A (x20 .root.1) (x21 .root.1)
   x22 .root.2 : refl A (x02 .root.1) (x12 .root.1)

Unsurprisingly, these two fields are related by symmetry: ``x22 .root.2`` is equal to ``(sym x22) .root.1`` and vice versa.  To implement this equality, in fact ``x22 .root.2`` computes to ``(sym x22) .root.1``.  (I don't know of a principled reason for a computation of this sort to go in one direction rather than the other; the present direction was just easier to implement.)  Recall also that ``sym x⁽ᵉᵉ⁾ = x⁽ᵉᵉ⁾``, from which it follows that ``x⁽ᵉᵉ⁾ .root.1 = x⁽ᵉᵉ⁾ .root.2``.

In general, a 1-dimensional field like ``root`` induces *n* fields of an *n*-dimenional version of a higher codatatype, distinguished by numerical suffixes from 1 to *n*. A 2-dimensional field, defined in the ``codata`` declaration as ``.field.ee``, induces (*n*)(*n*-1) fields of the *n*-dimensional version of the type, distinguished by numerical suffixes consisting of pairs of digits each from 1 to *n*. For instance, when *n*\ =3 the six fields are ``.field.12``, ``.field.13``, ``.field.23``, ``.field.21``, ``.field.32``, and ``.field.31``. As in the 1-dimensional case, all six of these fields are permuted by the symmetry operations acting on the object being projected, and to implement this equality all six of them compute to ``.field.12`` of a symmetrized input.

If any of the numbers goes above ``9``, then the suffix can start instead with ``..`` and the numbers be separated by additional periods.  In other words, ``.field.12`` is equivalent to ``.field..1.2`` but in the latter notation ``1`` and ``2`` can also be multi-digit numbers.  Whereas, the twelfth field of a 12-dimensional version of a higher codatatype induced by a 1-dimensional field can be written ``.field..12``.

When typechecking the type of a higher field in a `codata` definition, not only the argument variable but also all the *parameters in the context* are made higher-dimensional.  This is why we only defined ``√ℕ`` for a fixed constant type ``ℕ``: if we tried to define it with a parameter we would have trouble:

.. code-block:: none

   def √ (A : Type) : Type ≔ codata [
   | x .root.e : ?
   ]
   
    ￫ info[I0100]
    ￮ hole ?0 generated:
      
      A.0 : Type
      A.1 : Type
      A.2 : refl Type A.0 A.1
      x.0 : √ A.0
      x.1 : √ A.1
      x.2 : refl √ A.0 A.1 A.2 x.0 x.1
      ----------------------------------------------------------------------
      Type

So we can't write ``A`` in this hole, since that would be interpreted as ``A.2``, which is not a (0-dimensional) type until it is instantiated with elements of ``A.0`` and ``A.1``.  Thus we see that ``√`` is not fully internalizable, as usual for an "amazing right adjoint".  This degeneration of the context is essential, however, for arguably the most important example of a higher coinductive type, namely the definition of fibrancy in :ref:`Higher Observational Type Theory` as encoded in a substrate of internal binary parametricity.

When comatching against a higher coinductive type, the context is also degenerated when defining values for the higher fields.  For instance:

.. code-block:: none

   def t (x:A) : √ℕ ≔ [
   | .root.e ↦ ?
   ]
   
    ￫ info[I0100]
    ￮ hole ?0 generated:
      
      x.0 : ℕ
      x.1 : ℕ
      x.2 : refl ℕ x.0 x.1
      ----------------------------------------------------------------------
      ℕ

If comatching against a higher-dimensional version of a higher coinductive type, you must give a clause for all instances of each field whose dimensions may be only *partially* specified.  For instance:

.. code-block:: none

   def f : Id √ℕ n₀ n₁ ≔ [
   | .root.e ↦ ?
   | .root.1 ↦ ?
   ]

     ￫ info[I3003]
     ￮ hole ?0:
      
      ----------------------------------------------------------------------
      refl ℕ (refl n₀ .root.1) (refl n₁ .root.1)

     ￫ info[I3003]
     ￮ hole ?1:
      
      ----------------------------------------------------------------------
       ℕ

In other words, ``Id √ℕ n₀ n₁`` behaves like a higher coinductive type itself, which has one *ordinary* field ``root.1`` and one *higher* (1-dimensional) field ``root.e``.  Similarly, instances of ``Id (Id √ℕ)`` are higher coinductive types with two ordinary fields ``root.1`` and ``root.2`` and one higher field ``root.e``, and so on.


Displayed coinductive types
---------------------------

In the *displayed coinductive types* of *Displayed Type Theory* (dTT), the *output* of a corecursive method is a higher-dimensional version of the codatatype.  One of the most basic examples is the definition of the type of semi-simplicial types from the `dTT paper <https://arxiv.org/abs/2311.18781>`_:

.. code-block:: none

   def SST : Type ≔ codata [
   | X .z : Type
   | X .s : (X .z) → SST⁽ᵈ⁾ X
   ]

Narya permits displayed coinductives and their generalization to other kinds of parametricity.  Some examples can be found in the test directory `test/black/dtt.t <https://github.com/gwaithimirdain/narya/tree/master/test/black/dtt.t/>`_.
