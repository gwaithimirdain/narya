Parametric Observational Type Theory
====================================

There are many ways in which a type theory can be "higher-dimensional", by which we include homotopy type theory (specifically, Higher Observational Type Theory), internally parametric type theories, and `displayed type theory <https://arxiv.org/abs/2311.18781>`_.  The internal architecture of Narya is set up to eventually permit the user to mix and match multiple such "directions" of higher-dimensionality, but currently this is not realized.  At the moment, therefore, there is only one built-in direction, although its behavior is somewhat customizable.  We will first describe the current default behavior of this direction, which is *binary internal parametricity*, and then how it can be modified.

Identity/bridge types of canonical types
----------------------------------------

Every type ``A`` has a binary identity/bridge type denoted ``Id A x y``, and each term ``x:A`` has a reflexivity term ``refl x : Id A x x``.  (The argument of ``refl`` must synthesize.)  There is no built-in "transport" for these types (hence "bridge" is really a more appropriate name).  But they are "observational" in the sense that the identity/bridge type of a canonical type is another canonical type of the same sort.

For example, ``Id (A → B) f g`` is a function-type ``(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (g x₁)``.  In particular, ``refl f`` is a function of a type ``(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (f x₁)``, witnessing that all functions preserve "equalities" or "relatedness".  Thus the operation traditionally denoted ``ap`` in homotopy type theory is just ``refl`` applied to a function (although since the argument of ``refl`` must synthesize, if the function is an abstraction it must be ascribed).  Similarly, ``Id (A × B) u v`` is a type of pairs of identities, so if we have ``p : Id A (u .fst) (v .fst)`` and ``q : Id B (u .snd) (v .snd)`` we can form ``(p,q) : Id (A × B) u v``, and so on for other record types, datatypes, and codatatypes.

However, in Narya ``Id (A → B) f g`` does not *reduce* to the *ordinary* function-type ``(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (g x₁)``: instead it simply *behaves* like it, in the sense that its elements can be applied like functions and we can define elements of its as abstractions.  This should be compared with how ``Covec A 2`` doesn't reduce to ``A × (A × ⊤)`` but behaves like it in terms of what its elements are and what we can do with them.  In particular, ``Id (A → B) f g`` and ``(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → Id B (f x₀) (g x₁)`` are definitionally isomorphic, with the functions in both directions being η-expansions ``f ↦ (x₀ x₁ x₂ ↦ f x₀ x₁ x₂)``.  For most purposes this behavior is just as good as a reduction, and it retains more information about the type, which, as before, is useful for many purposes.  (In fact, with our current understanding, it appears to be *essential* for Narya's normalization and typechecking algorithms.)

The same is true for other canonical types, e.g. ``Id (A × B) u v`` does not reduce to ``Id A (u .fst) (v .fst) × Id B (u .snd) (v .snd)``, but it is *a* record type, with fields named ``fst`` and ``snd``, that is definitionally isomorphic to it by η-expansions.  Similarly, identity types of codatatypes behave like types of bisimulations: ``Id (Stream A) s t`` is a codatatype that behaves as if it were defined by

.. code-block:: none

   codata [
   | _ .head : Id A (s .head) (t .head)
   | _ .tail : Id (Stream A) (s. tail) (t .tail)
   ]

Individual bisimulations, i.e. elements of ``Id (Stream A) s t``, can then be constructed by comatching and corecursion.

In general, the fields, constructors, or methods of the identity/bridge type of a record type, datatype, or codatatype have the *same names* as those of the original type, and their types are the identity/bridge types of those of the original.

In the case of datatypes, the boundary (endpoints) of the identity/bridge type behave like *indices*.  Thus, for instance, ``Id ℕ`` behaves like an indexed datatype defined by

.. code-block:: none

   data [
   | zero. : Id ℕ zero. zero.
   | suc. : (n₀ n₁ : ℕ) (n₂ : Id ℕ n₀ n₁) → Id ℕ (suc. n₀) (suc. n₁)
   ]

Identity/bridge types of the universe
-------------------------------------

According to internal parametricity, we morally think of ``Id Type A B`` as being the type ``A → B → Type`` of correspondences.  (We avoid the word "relation" since it erroneously suggests proposition-valued.)  However, according to the above principles, we should expect ``Id Type A B`` to only *behave* like ``A → B → Type``, in that we can apply its elements to a pair of arguments in ``A`` and ``B`` to get a type, and define its elements by similarly abstracting.

The first is literally true: given ``R : Id Type A B`` and ``a:A``, ``b:B`` we have ``R a b : Type``.  We refer to this as *instantiating* the higher-dimensional type ``R``.  In fact, ``Id A x y`` itself is an instantiation, as we have ``Id A : Id Type A A``, which moreover is really just a notational variant of ``refl A``.

However, unlike a true function ``A → B → Type``, an element of ``Id Type A B`` cannot be "partially applied": you cannot write ``Id A a``.  But of course, you can η-expand it and write ``x ↦ Id A a x``.  (If there is demand, we might implement an automatic η-expansion of the former to the latter.)

For the second there is another wrinkle: we can define elements of ``Id Type A B`` by abstracting, but the body of the abstraction must be a *newly declared canonical type* rather than a pre-existing one.  This also seems to be essential to deal with symmetries (see :ref:`Symmetries and degeneracies`) in the normalization and typechecking algorithm.  Moreover, the current implementation allows this body to be a *record type* or *codatatype*, but not a *datatype*, and it does not permit other case tree operations in between such as pattern-matching.

For record types, there is a syntax that reflects this restriction: instead of the expected ``x y ↦ sig (⋯)`` we write ``sig x y ↦ (⋯)``, explicitly binding all the boundary variables as part of the record type syntax.  For example, here is the universal 1-dimensional record type, traditionally called "Gel":

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ ( ungel : R a b )

For codatatypes, we simply use the ordinary syntax, but the "self" variable automatically becomes a cube variable of the appropriate dimension (see :ref:`Cubes of variables`).

We may allow more flexibility in the future, but in practice the current restrictions do not seem very onerous.  For most applications, the above "Gel" record type can simply be defined once and used everywhere, rather than declaring new higher-dimensional types all the time.  Note that because record-types satisfy η-conversion, ``Gel A B R a b`` is definitionally isomorphic to ``R a b``.  Thus, ``Id Type A B`` contains ``A → B → Type`` as a "retract up to definitional isomorphism".  This appears to be sufficient for all applications of internal parametricity.  (``Id Type`` does not itself satisfy any η-conversion rule.)

Heterogeneous identity/bridge types
-----------------------------------

If ``B : A → Type``, then ``refl B x₀ x₁ x₂ : Id Type (B x₀) (B x₁)``.  Thus, given ``y₀ : B x₀`` and ``y₁ : B x₁``, we can instantiate this identification at them to obtain a type ``refl B x₀ x₁ x₂ y₀ y₁``. of *heterogeneous* identifications/bridges relating ``y₀`` and ``y₁`` "along" or "over" ``x₂``.  Since ``Id`` is a notational variant of ``refl``, this type can also be written suggestively as ``Id B x₀ x₁ x₂ y₀ y₁``.

Such heterogeneous identity/bridge types are used in the computation (up to definitional isomorphism) of identity/bridge types of *dependent* function types.  Specifically, ``Id ((x:A) → B x) f g`` acts like a function-type ``(x₀ x₁ : A) (x₂ : Id A x₀ x₁) → refl B x₀ x₁ x₂ (f x₀) (g x₁)``.  They also appear in identity/bridge types of other canonical types, such as when one field of a record type depends on previous ones.  For instance, ``Id (Σ A B) u v`` behaves like a record type

.. code-block:: none

   sig (
     fst : Id A (u .fst) (v .fst),
     snd : refl B (u .fst) (v .fst) fst (u .snd) (v .snd),
   )

More generally, since ``Σ : (A : Type) (B : A → Type) → Type``, we have ``refl Σ`` whose type is isomorphic to

.. code-block:: none

   (A₀ : Type) (A₁ : Type) (A₂ : Id Type A₀ A₁) (B₀ : A₀ → Type) (B₁ : A₁ → Type)
     (B₂ : refl ((X ↦ X → Type) : Type → Type) A₀ A₁ A₂ B₀ B₁)
     (u₀ : Σ A₀ B₀) (u₁ : Σ A₁ B₁) → Type

and ``refl Σ A₀ A₁ A₂ B₀ B₁ B₂ u₀ u₁`` behaves like a record type

.. code-block:: none

   sig (
     fst : A₂ (u₀ .fst) (u₁ .fst),
     snd : B₂ (u₀ .fst) (u₁ .fst) fst (u₀ .snd) (u₁ .snd),
   )

Here we have used the fact that the type of ``B₂`` is similarly isomorphic to

.. code-block:: none

   (x₀ : A₀) (x₁ : A₁) (x₂ : A₂ x₀ x₁) (y₀ : B₀ x₀) (y₁ : B₁ x₁) → Type

The ascription in the type of ``B₂`` is necessary since the argument of ``refl`` must synthesize, which abstractions do not.  This can be annoying to write, so an alternative is to use the built-in constant ``Π``:

.. code-block:: none

   B₂ : refl Π A₀ A₁ A₂ (x₀ ↦ Type) (x₁ ↦ Type) (x₀ x₁ x₂ ↦ refl Type) B₀ B₁

In particular, this is what Narya uses when printing higher-dimensional function-types (although it also uses :ref:`Cubes of variables`).


Higher-dimensional cubes
------------------------

Iterating ``Id`` or ``refl`` multiple times produces higher-dimensional cube types and cubes.  For instance, since ``Id A`` acts like a function ``A → A → Type``, *its* identity type or reflexivity type ``Id (Id A)`` acts as a function-type

.. code-block:: none

   (x₀₀ : A) (x₀₁ : A) (x₀₂ : Id A x₀₀ x₀₁)
     → (x₁₀ : A) (x₁₁ : A) (x₁₂ : Id A x₁₀ x₁₁)
     → (x₂₀ : Id A x₀₀ x₁₀) (x₂₁ : Id A x₀₁ x₁₁) → Type

We can view this as assigning to any boundary for a 2-dimensional square a type of fillers for that square.  Similarly, ``Id (Id (Id A))`` yields a type of 3-dumensional cubes, and so on.  Likewise, iterating ``refl`` on functions acts on these cubes: if ``f : A → B``, then

.. code-block:: none

   refl (refl f) : Id A a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁
     → Id B (f a₀₀) (f a₀₁) (refl f a₀₀ a₀₁ a₀₂) (f a₁₀) (f a₁₁) (refl f a₁₀ a₁₁ a₁₂)
              (refl f a₀₀ a₁₀ a₂₀) (refl f a₀₁ a₁₁ a₂₁)

More generally, just as any "1-dimensional type" ``A₂ : Id Type A₀ A₁`` can be instantiated at endpoints ``a₀:A₀`` and ``a₁:A₁`` to produce an ordinary (0-dimensional) type ``A₂ a₀ a₁ : Type``, any element ``A₂₂ : Id (Id Type) A₀₀ A₀₁ A₀₂ A₁₀ A₁₁ A₁₂ A₂₀ A₂₁`` can be instantiated at a "heterogeneous square boundary" consisting of

.. code-block:: none

   a₀₀ : A₀₀
   a₀₁ : A₀₁
   a₀₂ : A₀₂ a₀₀ a₀₁
   a₁₀ : A₁₀
   a₁₁ : A₁₁
   a₁₂ : A₁₂ a₁₀ a₁₁
   a₂₀ : A₂₀ a₀₀ a₁₀
   a₂₁ : A₂₁ a₀₁ a₁₁

to obtain an ordinary 0-dimensional type ``A₂₂ a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁`` whose elements are "heterogeneous squares".

We mentioned above that a 1-dimensional type cannot be "partially instantiated" such as ``Id A a₀``.  A higher-dimensional type *can* be partially instantiated, but not arbitrarily: you must give exactly enough arguments to reduce it to a type of some specific lower dimension.  For a 2-dimensional type such as ``A₂₂`` above, this means that in addition to its full 0-dimensional instantiations such as ``A₂₂ a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁``, it has partial 1-dimensional instantiations such as

.. code-block:: none

   A₂₂ a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ : Id Type (A₂₀ a₀₀ a₁₀) (A₂₁ a₀₁ a₁₁)

Note that this has exactly the right type that it can be *further* instantiated by ``a₂₀ a₂₁`` to produce a 0-dimensional type.  In fact, the fundamental operation is actually a "partial instantiation" that reduces the dimension by one; a "full instantiation" is just a sequence of these.

Symmetries and degeneracies
---------------------------

There is a symmetry operation ``sym`` that acts on at-least-two dimensional cubes, swapping or transposing the last two dimensions.  Like ``refl``, if the argument of ``sym`` synthesizes, then the ``sym`` synthesizes a symmetrized type; but in this case the argument must synthesize a "2-dimensional" type.  (The need to be able to "detect" 2-dimensionality here is roughly what imposes the requirements on our normalization/typechecking algorithm mentioned above.)  In addition, unlike ``refl``, an application of ``sym`` can also check if its argument does, since the type it is checked against can be "unsymmetrized" to obtain the necessary type for its argument to check against.

Combining versions of ``refl`` and ``sym`` yields arbitrary higher-dimensional "degeneracies" (from the BCH cube category).  There is also a generic syntax for such degeneracies, for example ``M⁽²ᵉ¹⁾`` or ``M^^(2e1)`` where the superscript represents the degeneracy, with ``e`` denoting a degenerate dimension and nonzero digits denoting a permutation.  (The ``e`` stands for "equality", since our ``Id`` is eventually intended to be the identity type of Higher Observational Type Theory.)  In the unlikely event you are working with dimensions greater than nine, you can separate multi-digit numbers and letters with a hyphen, e.g. ``M⁽¹⁻²⁻³⁻⁴⁻⁵⁻⁶⁻⁷⁻⁸⁻⁹⁻¹⁰⁾`` or ``M^^(0-1-2-3-4-5-6-7-8-9-10)``.  This notation can always synthesize if ``M`` does, while like ``sym`` it can also check if the degeneracy is a "pure permutation", consisting only of digits without any ``e`` s.

Degeneracies can be extended by identities on the left and remain the same operation.  For instance, the two degeneracies taking a 1-dimensional object to a 2-dimensional one are denoted ``1e`` and ``e1``, and of these ``1e`` can be written as simply ``e`` and coincides with ordinary ``refl`` applied to an object that happens to be 1-dimensional.  Similarly, the basic symmetry ``sym`` of a 3-dimensional object actually acts on the last two dimensions, so it coincides with the superscripted operation ``132``.

A mnemonic for the names of permutation operators is that the permutation numbers indicate the motion of arguments.  For instance, if we have a 3-dimensional cube

.. code-block:: none

   a222 : Id (Id (Id A))
     a000 a001 a002 a010 a011 a012 a020 a021 a022
     a100 a101 a102 a110 a111 a112 a120 a121 a122
     a200 a201 a202 a210 a211 a212 a220 a221

then to work out the boundary of a permuted cube such as ``a222⁽³¹²⁾``, consider the motion of the "axes" ``a001``, ``a010``, and ``a100``.  The permutation notation ``(312)`` denotes the permutation sending 1 to 3, sending 2 to 1, and sending 3 to 2.  Therefore, the first axis ``a001`` moves to the position previously occupied by the third axis ``a100``, the second axis ``a010`` moves to the position previously occupied by the first axis ``a001``, and the third axis ``a100`` moves to the position previously occupied by the second axis ``a010``.  This determines the motion of the other boundary faces (although not which of them end up symmetrized):

.. code-block:: none

   a222⁽³¹²⁾ : A⁽ᵉᵉᵉ⁾
     a000 a010 a020 a100 a110 a120 a200 a210 a220
     a001 a011 a021 a101 a111 a121 a201 a211 a221
     a002 a012 (sym a022) a102 a112 (sym a122) (sym a202) (sym a212)

Degeneracy operations are functorial.  For pure symmetries, this means composing permutations.  For instance, the "Yang-Baxter equation" holds, equating ``M⁽²¹³⁾⁽¹³²⁾⁽²¹³⁾`` with ``M⁽¹³²⁾⁽²¹³⁾⁽¹³²⁾``, as both reduce to ``M⁽³²¹⁾``.  Reflexivities also compose with permutations in a fairly straightforward way, e.g. ``M⁽¹ᵉ⁾⁽²¹⁾`` reduces to ``M^⁽ᵉ¹⁾``.

The principle that the identity/bridge types of a canonical type are again canonical types of the same sort applies also to symmetries and higher degeneracies of such types, with one exception.  To explain the exception, observe that ordinary canonical types are "intrinsically" 0-dimensional, and therefore any operations on them reduce to a "pure degeneracy" consisting entirely of ``e`` s, e.g. ``M⁽ᵉᵉ⁾⁽²¹⁾`` reduces to simply ``M⁽ᵉᵉ⁾``.  These pure degeneracies of canonical types are again canonical types of the same form, as discussed for ``Id`` and ``refl`` above.  However, an intrinsically higher-dimensional canonical type like ``Gel`` admits some degeneracies that permute the intrinsic dimension with some of the additional dimensions; the simplest of these is ``e1``.  These degeneracies of a higher-dimensional canonical type are *not* any longer canonical; but they are isomorphic to a canonical type by the action of a pure symmetry.

For instance, ``Gel A B R`` is a 1-dimensional type, belonging to ``Id Type A B``.  Thus, we can form the 2-dimensional type ``(Gel A B R)⁽ᵉ¹⁾``, and instantiate it using ``a₂ : Id A a₀ a₁`` and ``b₂ : Id B b₀ b₁`` and ``r₀ : R a₀ b₀`` and ``r₁ : R a₁ b₁`` to get a 0-dimensional type ``(Gel A B R)⁽ᵉ¹⁾ a₀ b₀ (r₀,) a₁ b₁ (r₁,) a₂ b₂``.  But this type is not canonical, and in particular not a record type; in particular given ``M : (Gel A B R)⁽ᵉ¹⁾ a₀ b₀ (r₀,) a₁ b₁ (r₁,) a₂ b₂`` we cannot write ``M .ungel``.  However, we have ``sym M : (Gel A B R)⁽¹ᵉ⁾ a₀ a₁ a₂ b₀ b₁ b₂ (r₀,) (r₁,)``, which doesn't permute the intrinsic dimension ``1`` with the degenerate dimension ``e`` and *is* therefore a record type, and so we can write ``sym M .ungel``, which has type ``Id R a₀ a₁ a₂ b₀ b₁ b₂ r₀ r₁``.  In addition, since ``(Gel A B R)⁽ᵉ¹⁾ a₀ b₀ (r₀,) a₁ b₁ (r₁,) a₂ b₂`` is *isomorphic* to this record type, it also satisfies an eta-rule: two of its terms ``M`` and ``N`` are definitionally equal as soon as ``sym M .ungel`` and ``sym N .ungel`` are.

Implicit boundaries
-------------------

Until now we have been writing all the arguments of higher-dimensional types and functions explicitly.  There are times when this is necessary, but it is clear that in many cases it is redundant.  For instance, in ``refl f a₀ a₁ a₂``, since the type of ``a₂`` must be ``Id A a₀ a₁``, if we know this type (that is, if ``a₂`` synthesizes) then ``a₀`` and ``a₁`` are uniquely determined.

In general, this is the sort of issue that implicit arguments and higher-order unification are designed to deal with.  Narya does not yet have either of these features in general, but it does have a specialized version that essentially uses bidirectional typechecking to synthesize the redundant parts of boundaries in higher-dimensional function applications and type instantiations.  This feature is currently off by default; it can be turned on with the two commands

.. code-block:: none

   option function boundaries ≔ implicit
   option type boundaries ≔ implicit

(and back off again with the similar ``≔ explicit`` commands).

When *function* boundaries are implicit, a higher-dimensional function application takes only *one* argument, the top-dimensional one; thus instead of ``refl f a₀ a₁ a₂`` you can (and must) write ``refl f a₂``, and instead of ``refl (refl f) a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂`` you can (and must) write ``refl f a₂₂``.  It is possible to give the implicit arguments explicitly by surrounding them with curly braces, as in ``refl f {a₀} {a₁} a₂``, but if you do this you must give *all* of them explicitly; there are no half measures.  The main reason you might need to do this is if ``a₂`` is a term that doesn't synthesize, since in that case ``refl f a₂`` won't be able to infer the boundaries ``a₀`` and ``a₁``.

When *type* boundaries are implicit, a full instantiation of a higher-dimensional type takes only the *highest-dimensional* arguments.  For ordinary 1-dimensional identity types, this changes nothing, since both arguments ``a₀`` and ``a₁`` of ``Id A a₀ a₁`` are 0-dimensional and that is the highest dimension of any argument.  But for squares, instead of ``Id (Id A) a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁`` you can (and must) write ``Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁`` since these are the four 1-dimensional arguments; the 0-dimensional ones are inferred from their boundaries (which are required to match up correctly where they overlap).  And you can of course give them explicitly with ``Id (Id A) {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁``.  In this case there are some half measures: if you give any lower-dimensional argument explicitly you must give all the arguments in that "block" explictly, but you can omit those in other blocks; for instance you can write ``Id (Id A) {a₀₀} {a₀₁} a₀₂ a₁₂ a₂₀ a₂₁`` or ``Id (Id A) a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁``.

Normally, when boundaries are implicit, Narya also *prints* higher-dimensional function applications and type instantiations with the lower-dimensional boundaries omitted.  However, you can tell it to print these arguments explicitly with the commands

.. code-block:: none

   display function boundaries ≔ on
   display type boundaries ≔ on

(and switch back with ``≔ off``).  These commands are not available in source files, since they should not be un-done; they can be given in interactive mode, or in ProofGeneral with ``C-c C-v``, or you can use the corresponding command-line flags such as ``-show-function-boundaries``.  When these options are ``on`` *and* implicitness for the relevant kinds of boundaries is also on, Narya prints *all* the lower-dimensional arguments explicitly, with curly braces around them.  There are no half measures here, for functions or for types.  In the future, we may implement a way to switch on such display for some constants and/or variables but not others.

In addition, even when printing implicit boundaries is off, Narya attempts to be smart and print those boundaries when it thinks that they would be necessary in order to re-parse the printed term, because the corresponding explicit argument isn't synthesizing.  In this case it can do half measures, the way you can when writing type boundaries: the implicit arguments in each "block" are printed only if the primary argument of that block is nonsynthesizing.


Cubes of variables
------------------

Implicitness of arguments to higher-dimensional *applications* has no bearing on higher-dimensional *abstractions*: the "implicit arguments" still must be named in an abstraction in the usual way, regardless of whether implicitness is on or not.  (This will also be Narya's approach to implicit arguments more generally.)  However, there is a different shorthand syntax for higher-dimensional abstractions: instead of ``x₀ x₁ x₂ ↦ M`` you can write ``x ⤇ M`` (or ``x |=> M`` in ASCII).  This binds ``x`` as a "family" or "cube" of variables whose names are suffixed with face names in ternary notation: ``x.0`` and ``x.1`` and ``x.2``, or in higher dimensions ``x.00`` through ``x.22`` and so on.  (The dimension is inferred from the type at which the abstraction is checked.)  Note that this is a *purely syntactic* abbreviation: there is no object "``x``", but rather there are really *three different variables* that just happen to have the names ``x.0`` and ``x.1`` and ``x.2``.  (There is no potential for collision with user-defined names, since ordinary local variable names cannot contain internal periods, and atomic identifiers cannot consist entirely of digits.)

These "cube variables" also appear automatically when matching against a higher-dimensional version of a datatype.  For instance, we can do an encode-decode proof for the natural numbers by matching directly on ``Id ℕ`` (using pattern-matching abstractions):

.. code-block:: none

   def code : ℕ → ℕ → Type ≔
   [ zero. ↦ [ zero. ↦ sig ()
             | suc. n ↦ data [] ]
   | suc. m ↦ [ zero. ↦ data []
              | suc. n ↦ sig ( uncode : code m n ) ]]
   
   def decode : (m n : ℕ) → code m n → Id ℕ m n ≔
   [ zero. ↦ [ zero. ↦ _ ↦ zero.
             | suc. n ↦ [] ]
   | suc. m ↦ [ zero. ↦ []
              | suc. n ↦ p ↦ suc. (decode m n (p .0)) ]]
   
   def encode (m n : ℕ) : Id ℕ m n → code m n ≔
   [ zero. ↦ ()
   | suc. p ↦ (_ ≔ encode p.0 p.1 p.2)]

Here in the definition of ``encode``, the pattern variable ``p`` of the ``suc.`` branch is automatically made into a 1-dimensional cube of variables since we are matching against an element of ``Id ℕ``, so in the body we can refer to ``p.0``, ``p.1``, and ``p.2``.  In the future, we may implement a dual syntax for simultaneously *applying* a higher-dimensional function to a whole cube of variables of this sort as well, although of course if implicit application is on you can just write ``refl f x.2`` and so on.

Similarly, when defining a codatatype lying in a higher universe, the "self" variable automatically becomes a cube variable, so that the boundary of the type is accessible through its faces.  For instance, here is a codatatype version of Gel:

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ codata [ x .ungel : R x.0 x.1 ]

Varying the behavior of parametricity
-------------------------------------

The parametricity described above, which is Narya's default, is *binary* in that the identity/bridge type ``Id A x y`` takes *two* elements of ``A`` as arguments.  However, a different "arity" can be specified with the ``-arity`` command-line flag.  For instance, under ``-arity 1`` we have bridge types ``Id A x``, and under ``-arity 3`` they look like ``Id A x y z``.  Everything else also alters according, e.g. under ``-arity 1`` the type ``Id (A → B) f`` is isomorphic to ``(x : A) (x' : Id A x) → Id B (f x)``, and a cube variable has pieces numbered with only ``0`` s and ``1`` s.

In principle, the arity could be any natural number, but for syntactic reasons Narya currently requires it to be between 1 and 9 inclusive.  The problem with arities greater than 9 is that the syntax ``x.10`` for cube variables would become ambiguous: does ``10`` mean "one-zero" or "ten"?  But if you have an application of such a type theory, let us know and we can work out a syntax (although at present we are unaware of any applications of n-ary parametricity for n>2).  The problem with arity 0 is that then ``Id A`` would belong to ``Id Type`` and also be instantiatable to an element of ``Type``, but since this requires no arguments it's not clear what syntax should indicate whether the instantiation has happened.  We do expect to solve this problem somehow, since 0-ary parametricity does have potential applications (it is related to nominal type theory).

It is also possible to rename or remove the primitives ``refl`` and ``Id`` (which, recall, is just another notation for ``refl``), as well as change the letter ``e`` used in generic degeneracies.  The default behavior is equivalent to the command-line argument ``-direction e,refl,Id``; in general the argument of ``-direction`` is a comma-separated list of names, where the first must be a single lowercase letter to be used in generic degeneracies, and the others (if any) are names for the basic degeneracy.  For instance, in unary parametricity we might write ``-arity 1 -direction r,red`` and think of ``red x`` as "``x`` is reducible".

The name of ``sym`` cannot be changed or removed, and likewise for the digits used in generic degeneracies to indicate permuted dimensions.

Finally, parametricity can be set to be *internal* (the default) or *external*.  Setting it to external instead means that dimension-changing degeneracies (including ``refl``, but not ``sym``) can only be applied to *closed terms*.  Since degeneracies also compute fully on closed terms (at least in the "up-to-definitional-isomorphism" sense), we can then more or less think of these operations as meta-operations on syntax rather than intrinsic aspects of the theory.  This is the usual meaning of "external parametricity", although Narya's is of course at least partially internalized.  (Semantically, what Narya calls "external parametricity" is modeled in a diagram of *semi-cubical* types, in contrast to internal parametricity which is modeled in *cubical* types.)

In addition, under external parametricity, *axioms* are not permitted to be used inside of dimension-changing degeneracies either.  The reasoning behind this is that we may want to assume axioms that are inconsistent with parametricity, such as excluded middle, while still making use of external parametricity on other types.  (Note that *internal* parametricity is nonclassical, actively contradicting excluded middle.)  It also maintains the principle that assuming an axiom of type `A` is equivalent to working in a context extended by a variable of type `A`.  However, in the future it may be possible to declare a special kind of "parametric axiom" that does have higher-dimensional versions.

The combination ``-arity 1 -direction d -external`` is a version of `displayed type theory <https://arxiv.org/abs/2311.18781>`_ (dTT), and as such can be selected with the single option ``-dtt``.  The primary differences between ``narya -dtt`` and the original dTT of the paper are:

1. Narya currently has no modalities, so display can only be applied to closed terms rather than to the more general □-modal ones.
2. Narya has symmetries, which in particular (as noted in the paper) makes ``SST⁽ᵈ⁾`` (see :ref:`Displayed coinductive types`) actually usable.
3. As noted above, display in Narya computes only up to isomorphism, and in the case of ``Type`` only up to retract up to isomorphism.
4. (A syntactic difference only) Generic degeneracies in Narya must be parenthesized, so we write ``A⁽ᵈ⁾`` instead of ``Aᵈ``.


Parametrically discrete types
-----------------------------

Discreteness is an experimental (and probably temporary) feature.  A (strictly parametrically) *discrete* type, in the sense meant here, is one whose higher-dimensional versions are all definitionally subsingletons.  That is, if ``b1 : A⁽ᵈ⁾ a`` and ``b2 : A⁽ᵈ⁾ a``, then ``b1`` and ``b2`` are convertible (this is implemented as an η-rule).  Discreteness is currently restricted to arity 1 (including dTT), and can be enabled by the ``-discreteness`` flag (which is not included in ``-dtt``).  When discreteness is enabled, a mutual family of datatypes will be marked as discrete if

1. All elements of the mutual family are datatypes; and
2. The types of all of their parameters, indices, and constructor arguments are either types belonging to the same family or previously defined discrete datatypes.

Of the datatypes we have mentioned as examples, the discrete ones are ``ℕ``, ``Bool``, and ``⊥``.  Some other examples of discrete types are integers and binary trees:

.. code-block:: none

   def ℤ : Type ≔ data [
   | zero.
   | suc. (_:ℕ)
   | negsuc. (_:ℕ)
   ]
   
   def btree : Type ≔ data [
   | leaf.
   | node. (_:btree) (_:btree)
   ]

A family of datatypes indexed by discrete types can be discrete, such as inequality of natural numbers:

.. code-block:: none

   def ℕ.le : (k n : ℕ) → Type := data [
   | zero. (n : ℕ) : ℕ.le zero. n
   | suc. (k n : ℕ) (_ : ℕ.le k n) : ℕ.le (suc. k) (suc. n)
   ]

So can a mutual family of types:

.. code-block:: none

   def even : ℕ → Type ≔ data [
   | zero. : even zero. 
   | suc. (n : ℕ) (_ : odd n) : even (suc. n) 
   ]
   
   and odd : ℕ → Type ≔ data [
   | suc. (n : ℕ) (_ : even n) : odd (suc. n)
   ]

The higher-dimensional versions of a discrete datatype are also still themselves datatypes, so they have constructors and can be matched on.  In fact it should be possible to prove internally *without* ``-discreteness`` that these types are always propositionally contractible.  In particular, they are inhabited, so discreteness just adds some strictness, making them *definitionally* singletons.  For example, here is the proof that the displayed versions of ``ℕ`` are inhabited:

.. code-block:: none

   def ℕ.d (n : ℕ) : ℕ⁽ᵈ⁾ n ≔ match n [
   | zero. ↦ zero.
   | suc. n ↦ suc. (ℕ.d n)
   ]


Currently, the test for discreteness is performed immediately and only upon completion of the ``def`` command that defines a family of datatypes.  In particular, if the definition of a datatype contains a hole, it will not be considered discrete, even if the hole is later filled to make the definition one that would have been discrete if given from the get-go.  This could in theory be improved, but I am more likely to feel like putting effort into implementing the "correct" replacement for discrete types, namely modally-guarded parametricity such as full dTT.  Note that if you are using :ref:`ProofGeneral mode` (as you should be), you can just retract and re-process the ``def`` command after filling all the holes in it, and it will then be discrete.

