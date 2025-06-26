Parametricity
=============

Narya's support for parametricity builds on the primitives discussed in :ref:`Observational higher dimensions`.  The defining feature of parametricity is then that a higher-dimensional type such as ``A₂ : Id Type A₀ A₁`` is *completely characterized* by its instantiations ``A₂ a₀ a₁``, so that ``Id Type A₀ A₁`` is *equivalent* to the type ``A₀ → A₁ → Type`` of correspondences.  For this reason we usually use a different notation.

Names for parametricity
-----------------------

The command-line flag ``-direction`` can be used to rename or remove the formally-synonymous primitives ``refl``, ``Id``, and ``ap``, as well as the superscript letter ``e``.  The default behavior described in :ref:`Observational higher dimensions` is equivalent to the command-line argument ``-direction e,refl,Id,ap``.  In general the argument of ``-direction`` is a comma-separated list of names, where the first must be a single lowercase letter to be used in generic degeneracies, and the others (if any) are names for the basic degeneracy.  If there is a second name such as ``refl``, it is used as the default for 1-dimensional degeneracies.  If there is a third name such as ``Id``, it is used for 1-dimensional degeneracies of types and type families.  And if there is a fourth name such as ``ap``, it is used for 1-dimensional degeneracies of other functions.  (The name of ``sym`` cannot be changed or removed, and likewise for the digits used in generic degeneracies to indicate permuted dimensions.)

In the rest of our discussion of parametricity we will assume the flag

.. code-block:: none

   -direction p,rel,Br

where ``p`` stands for *parametricity*, ``rel`` for *relation* or *relatedness*, and ``Br`` for *bridge* types.  In this notation, we now restate the defining feature of parametricity: a higher-dimensional type such as ``A₂ : Br Type A₀ A₁`` is completely characterized by its instantiations ``A₂ a₀ a₁``, so that ``Br Type A₀ A₁`` is equivalent to the type ``A₀ → A₁ → Type`` of correspondences.


Bridge types of the universe
----------------------------

This principle suggests that we should be able to *introduce* elements of ``Br Type A₀ A₁`` by abstraction such as ``x₀ x₁ ↦ …``.  However, if allowed unrestrictedly, this would lead to instantiations of higher-dimensional types *reducing* to syntaxes that cannot be easily recognized as such, which would cause problems for Narya's typechecker.  Therefore, we impose the requirement that the body of such an abstraction must be a *newly declared canonical type* rather than a pre-existing one.  Moreover, the current implementation allows this body to be a *record type* or *codatatype*, but not a *datatype*, and it does not permit other case tree operations in between such as pattern-matching.  We call these *higher-dimensional record types* or *codatatypes*.

In the case of record types, there is a syntax that reflects this restriction: instead of the expected ``x y ↦ sig (⋯)`` we write ``sig x y ↦ (⋯)``, explicitly binding all the boundary variables as part of the record type syntax.  For example, here is the universal 1-dimensional record type, traditionally called "Gel":

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Br Type A B ≔ sig a b ↦ ( ungel : R a b )

For codatatypes, we simply use the ordinary syntax, but the "self" variable automatically becomes a cube variable of the appropriate dimension.  For instance, here is a codatatype version of Gel:

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Br Type A B ≔ codata [ x .ungel : R x.0 x.1 ]

We may allow more flexibility in the future, but in practice the current restrictions do not seem very onerous.  For most applications, the above "Gel" record type can simply be defined once and used everywhere, rather than declaring new higher-dimensional types all the time.  Note that because record-types satisfy η-conversion, ``Gel A B R a b`` is definitionally isomorphic to ``R a b``.  Thus, ``Br Type A B`` contains ``A → B → Type`` as a "retract up to definitional isomorphism".  This appears to be sufficient for all applications of internal parametricity.  (``Br Type`` does not itself satisfy any η-conversion rule.)

There is one additional subtlety involving higher-dimensional record and codata types, specifically in their degeneracies.  Since ordinary canonical types are "intrinsically" 0-dimensional, any degeneracy operations on them reduce to a "pure degeneracy" consisting entirely of ``p`` s, e.g. ``M⁽ᵖᵖ⁾⁽²¹⁾`` reduces to simply ``M⁽ᵖᵖ⁾``.  These *pure* degeneracies of canonical types are again canonical types of the same form, as discussed in :ref:`Observational higher dimensions`.

However, an intrinsically higher-dimensional canonical type like ``Gel`` admits some degeneracies that permute the intrinsic dimension with some of the additional dimensions.  The simplest of these degeneracies is ``p1``.  These degeneracies of a higher-dimensional canonical type are *not* any longer canonical; but they are isomorphic to a canonical type by the action of a pure symmetry.

For instance, ``Gel A B R`` is a 1-dimensional type, belonging to ``Br Type A B``.  Thus, we can form the 2-dimensional type ``(Gel A B R)⁽ᵖ¹⁾``, and instantiate it using ``a₂ : Br A a₀ a₁`` and ``b₂ : Br B b₀ b₁`` and ``r₀ : R a₀ b₀`` and ``r₁ : R a₁ b₁`` to get a 0-dimensional type ``(Gel A B R)⁽ᵖ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂``.  But this type is not canonical, and in particular not a record type; in particular given ``M : (Gel A B R)⁽ᵖ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂`` we cannot write ``M .ungel``.  However, we have ``sym M : (Gel A B R)⁽¹ᵖ⁾ {a₀} {a₁} a₂ {b₀} {b₁} b₂ (r₀,) (r₁,)``, which doesn't permute the intrinsic dimension ``1`` with the degenerate dimension ``p`` and *is* therefore a record type, and so we can write ``sym M .ungel``, which has type ``Br R a₂ b₂ r₀ r₁``.  In addition, since ``(Gel A B R)⁽ᵖ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂`` is *isomorphic* to this record type, it also satisfies an eta-rule: two of its terms ``M`` and ``N`` are definitionally equal as soon as ``sym M .ungel`` and ``sym N .ungel`` are.


Varying the arity of parametricity
----------------------------------

The parametricity described above, which is Narya's default, is *binary* in that the bridge type ``Br A x y`` takes *two* elements of ``A`` as arguments.  However, a different "arity" can be specified with the ``-arity`` command-line flag.  For instance, under ``-arity 1`` we have bridge types ``Br A x``, and under ``-arity 3`` they look like ``Br A x y z``.  Everything else also alters according, e.g. under ``-arity 1`` the type ``Br (A → B) f`` is isomorphic to ``{x₀ : A} (x₁ : Br A x) → Br B (f x)``, and a cube variable has pieces numbered with only ``0`` s and ``1`` s.

In principle, the arity could be any natural number, but for syntactic reasons Narya currently requires it to be between 0 and 9 inclusive.  The problem with arities greater than 9 is that the syntax ``x.10`` for cube variables would become ambiguous: does ``10`` mean "one-zero" or "ten"?  It would probably be possible to resolve this similarly to how we deal with degeneracies for dimensions above 9, for instance writing ``x..1.0`` for one-zero and ``x..10`` for ten (while keeping the simpler ``x.10`` to mean ``x..1.0``), but this is not a priority because at present we are unaware of any applications of n-ary parametricity for n>2.

Syntactically, nullary parametricity is a bit special because when instantiating a higher-dimensional type there are zero arguments to be supplied, so it is not obvious how to indicate that an instantiation has happened.  To resolve this, each dimension of instantiation that takes zero arguments is indicated by syntactic application to a dot ``.`` that denotes "zero arguments".  Thus, if ``A : Type`` then ``Br A : Type⁽ᵖ⁾ .``, and if ``a : A`` then ``rel a : A⁽ᵖ⁾ .``, while ``rel (rel a) : A⁽ᵖᵖ⁾ . .``, and so on.  Note that each dot must be separated from others by spaces.


Internal versus external parametricity
--------------------------------------

Parametricity can also be set to be *internal* or *external* with the like-named flags ``-internal`` and ``-external``.  Internal is the default and the behavior that we have described up until now.  Setting it to external instead means that dimension-changing degeneracies (such as ``rel``, but not ``sym``) can only be applied to *closed terms*.  Since degeneracies also compute fully on closed terms (at least in the "up-to-definitional-isomorphism" sense), we can then more or less think of these operations as meta-operations on syntax rather than intrinsic aspects of the theory.  This is the usual meaning of "external parametricity", although Narya's is of course at least partially internalized.  (Semantically, what Narya calls "external parametricity" is modeled in a diagram of *semi-cubical* types, in contrast to internal parametricity which is modeled in *cubical* types.)

In addition, when parametricity is external, *axioms* are not permitted to be used inside of dimension-changing degeneracies either, nor are any constants that use axioms in their types or definitions, hereditarily.  That is, axioms are "nonparametric" and have no dimension-changing degeneracies, and any definition that uses a nonparametric constant is also nonparametric.  Similarly, if any of the definitions in a mutual block use a nonparametric constant, then all the constants in the mutual block are nonparametric.

The reasoning behind this is that you may want to assume axioms that are inconsistent with parametricity, such as excluded middle, while still making use of external parametricity on other types.  (Note that *internal* parametricity is nonclassical, actively contradicting excluded middle.)  It also maintains the principle that assuming an axiom of type `A` is equivalent to working in a context extended by a variable of type `A`.  However, in the future it may be possible to declare a special kind of "parametric axiom" that does have higher-dimensional versions.

When a definition contains :ref:`holes` but does not (yet) use any nonparametric constants, it is considered parametric, and hence can have dimension-changing degeneracies applied to it.  Therefore, if you later try to fill one of those holes with a term that uses a nonparametric constant, an error will be emitted; it is not possible to retroactively set a definition to be nonparametric since it might already have had dimension-changing degeneracies applied to it by other definitions.  In this case, you have to undo back to the original definition and manually copy your desired nonparametric term in place of the hole.  (If there is significant demand, we may implement an easier solution.)


Parametrically discrete types
-----------------------------

Discreteness is an experimental (and probably temporary) feature.  A (strictly parametrically) *discrete* type, in the sense meant here, is one whose higher-dimensional versions are all definitionally subsingletons.  That is, if ``b1 : A⁽ᵈ⁾ a`` and ``b2 : A⁽ᵈ⁾ a``, then ``b1`` and ``b2`` are convertible (this is implemented as an η-rule).  Discreteness is currently restricted to arity 1 (including dTT), and can be enabled by the ``-discreteness`` flag.  When discreteness is enabled, a mutual family of datatypes will be marked as discrete if

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

