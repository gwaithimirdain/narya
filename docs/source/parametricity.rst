Parametricity
=============

Narya's support for parametricity builds on the primitives discussed in :ref:`Observational higher dimensions`.  The defining feature of parametricity is then that a higher-dimensional type such as ``A₂ : Id Type A₀ A₁`` is *completely characterized* by its instantiations ``A₂ a₀ a₁``, so that ``Id Type A₀ A₁`` is *equivalent* to the type ``A₀ → A₁ → Type`` of correspondences.  For this reason we usually use a different notation.

Names for parametricity
-----------------------

Parametricity mode is activated by the command-line flag ``-parametric``.  In addition, when this flag is given, the command-line flag ``-direction`` can be used to rename or remove the formally-synonymous primitives ``refl``, ``Id``, and ``ap``, as well as the superscript letter ``e``.  The notation of HOTT, which we used in :ref:`Observational higher dimensions` and is the default if no ``-direction`` argument is given, is equivalent to the command-line argument ``-direction e,refl,Id,ap``.  In general, the argument of ``-direction`` is a comma-separated list of names, where the first must be a single lowercase letter to be used in generic degeneracies, and the others (if any) are prefix names for the basic degeneracy.  If there is a second name such as ``refl``, it is used as the default for 1-dimensional degeneracies.  If there is a third name such as ``Id``, it is used for 1-dimensional degeneracies of types and type families.  And if there is a fourth name such as ``ap``, it is used for 1-dimensional degeneracies of other functions.  (The name of ``sym`` cannot be changed or removed, and likewise for the digits used in generic degeneracies to indicate permuted dimensions.)

In the rest of our discussion of parametricity we will assume the flags

.. code-block:: none

   -parametric -direction p,rel,Br

where ``p`` stands for *parametricity*, ``rel`` for *relation* or *relatedness*, and ``Br`` for *bridge* types.  In this notation, we now restate the defining feature of parametricity: a higher-dimensional type such as ``A₂ : Br Type A₀ A₁`` is completely characterized by its instantiations ``A₂ a₀ a₁``, so that ``Br Type A₀ A₁`` is equivalent to the type ``A₀ → A₁ → Type`` of correspondences.

In particular, when working in parametricity mode you may want to start all your source files with a line such as

.. code-block:: none

   {` -*- narya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- `}

Remember that this is a directive to Emacs, not to Narya, so that after adding it to the top of a new file you must run ``M-x normal-mode`` to load it, and when switching from one file to another with a different set of flags you must quit ProofGeneral entirely with ``C-c C-x``.


Bridge types of the universe
----------------------------

The above principle of parametricity suggests that we should be able to *introduce* elements of ``Br Type A₀ A₁`` by abstraction such as ``x₀ x₁ ↦ …``.  However, if allowed unrestrictedly, this would lead to instantiations of higher-dimensional types *reducing* to syntaxes that cannot be easily recognized as such, which would cause problems for Narya's typechecker.  Therefore, we impose the requirement that the body of such an abstraction must be a *newly declared canonical type* rather than a pre-existing one.  Moreover, the current implementation allows this body to be a *record type* or *codatatype*, but not a *datatype*, and it does not permit other case tree operations in between such as pattern-matching.

We call these *higher-dimensional record types* or *codatatypes*.  Their definition is almost the same as an ordinary record type or codatatype, except that (1) they belong to a (fully instantiated) bridge type of the universe rather than to the universe itself, (2) they must be defined using :ref:`self variable syntax <Self variables for record types>` even in the case of record types, and (3) the self variable becomes a :ref:`cube variable <Cubes of variables>` representing elements of the boundary as well as the "actual" self variable at the top face.

For example, here is the universal 1-dimensional record type, traditionally called ``Gel``:

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Br Type A B ≔ sig ( a .ungel : R a.0 a.1 )

*(An older alternative syntax* ``sig a b ↦ ( ungel : R a b )`` *is now deprecated.)*

We may allow more flexibility in the future, but in practice the current restrictions do not seem very onerous.  For most applications, the above ``Gel`` record type can simply be defined once and used everywhere, rather than declaring new higher-dimensional types all the time.

In particular, note that because record-types satisfy η-conversion, ``Gel A B R a b`` is definitionally isomorphic to ``R a b``.  Thus, ``Br Type A B`` contains ``A → B → Type`` as a "retract up to definitional isomorphism".  This appears to be sufficient for all applications of internal parametricity.  (``Br Type`` does not itself satisfy any η-conversion rule.)

There is one additional subtlety involving higher-dimensional record and codata types, specifically in their degeneracies.  Since ordinary canonical types are "intrinsically" 0-dimensional, any degeneracy operations on them reduce to a "pure degeneracy" consisting entirely of ``p`` s, e.g. ``M⁽ᵖᵖ⁾⁽²¹⁾`` reduces to simply ``M⁽ᵖᵖ⁾``.  These *pure* degeneracies of canonical types are again canonical types of the same form, as discussed in :ref:`Observational higher dimensions`.

However, an intrinsically higher-dimensional canonical type like ``Gel`` admits some degeneracies that permute the intrinsic dimension with some of the additional dimensions.  The simplest of these degeneracies is ``p1``.  These degeneracies of a higher-dimensional canonical type are *not* any longer canonical; but they are isomorphic to a canonical type by the action of a pure symmetry.

For instance, ``Gel A B R`` is a 1-dimensional type, belonging to ``Br Type A B``.  Thus, we can form the 2-dimensional type ``(Gel A B R)⁽ᵖ¹⁾``, and instantiate it using ``a₂ : Br A a₀ a₁`` and ``b₂ : Br B b₀ b₁`` and ``r₀ : R a₀ b₀`` and ``r₁ : R a₁ b₁`` to get a 0-dimensional type ``(Gel A B R)⁽ᵖ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂``.  But this type is not canonical, and in particular not a record type; in particular given ``M : (Gel A B R)⁽ᵖ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂`` we cannot write ``M .ungel``.  However, we have ``sym M : (Gel A B R)⁽¹ᵖ⁾ {a₀} {a₁} a₂ {b₀} {b₁} b₂ (r₀,) (r₁,)``, which doesn't permute the intrinsic dimension ``1`` with the degenerate dimension ``p`` and *is* therefore a record type, and so we can write ``sym M .ungel``, which has type ``Br R a₂ b₂ r₀ r₁``.  In addition, since ``(Gel A B R)⁽ᵖ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂`` is *isomorphic* to this record type, it also satisfies an eta-rule: two of its terms ``M`` and ``N`` are definitionally equal as soon as ``sym M .ungel`` and ``sym N .ungel`` are.


Varying the arity of parametricity
----------------------------------

The parametricity described above, which is Narya's default, is *binary* in that the bridge type ``Br A x y`` takes *two* elements of ``A`` as arguments.  However, a different "arity" can be specified with the ``-arity`` command-line flag (which also requires the ``-parametric`` flag).  For instance, under ``-arity 1`` we have bridge types ``Br A x``, and under ``-arity 3`` they look like ``Br A x y z``.  Everything else also alters according, e.g. under ``-arity 1`` the type ``Br (A → B) f`` is isomorphic to ``{x₀ : A} (x₁ : Br A x) → Br B (f x)``, and a cube variable has pieces numbered with only ``0`` s and ``1`` s.  This also applies to higher-dimensional types, for instance in arity 1 the definition of ``Gel`` is

.. code-block:: none

   def Gel (A : Type) (R : A → Type) : Br Type A ≔ sig ( a .ungel : R a.0 )

Semantically, parametric Narya with arity *n* has a model in the topos of *n*-ary semicartesian cubical sets (or spaces, or objects of some other topos).  Semicartesian cubical sets have faces, degeneracies, and symmetries, but no diagonals or connections, and to say they are *n*-ary means that each 1-cube has *n* "endpoints".  For instance, 1-ary cubes can be thought of as powers of a half-open interval; the category of 1-ary cubes happens to be equivalent to the category of augmented symmetric simplicial sets.

In principle, the arity could be any natural number, but for syntactic reasons Narya currently requires it to be between 0 and 9 inclusive.  The problem with arities greater than 9 is that the syntax ``x.10`` for cube variables would become ambiguous: does ``10`` mean "one-zero" or "ten"?  It would probably be possible to resolve this similarly to how we deal with degeneracies for dimensions above 9, for instance writing ``x..1.0`` for one-zero and ``x..10`` for ten (while keeping the simpler ``x.10`` to mean ``x..1.0``), but this is not a priority because at present we are unaware of any applications of n-ary parametricity for n>2.

Syntactically, nullary parametricity is a bit special because when instantiating a higher-dimensional type there are zero arguments to be supplied, so it is not obvious how to indicate that an instantiation has happened.  To resolve this, each dimension of instantiation that takes zero arguments is indicated by syntactic application to a dot ``.`` that denotes "zero arguments".  Thus, if ``A : Type`` then ``Br A : Type⁽ᵖ⁾ .``, and if ``a : A`` then ``rel a : A⁽ᵖ⁾ .``, while ``rel (rel a) : A⁽ᵖᵖ⁾ . .``, and so on.  Note that each dot must be separated from others by spaces.
