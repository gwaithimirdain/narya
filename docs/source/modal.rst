Modal type theory
=================

Just as type theory can be regarded as a generalization of logic, with types being a generalization of propositions, *modal type theory* is a generalization of modal logic.  Specifically, just as modal logic is enhanced with one or more *modal operators*, which are unary operations on propositions, modal type theory is enhanced with similar unary operations on types.


Mode theories
-------------

The most classical operators in modal logic are "it is necessary that" (traditionally written □) and "it is possible that" (traditionally written ◇), but modern modal logic studies many other operators as well.  Similarly, in modal type theory there are many different kinds of modal operators; a common example is that when types are regarded as having some kind of "topological" or "cohesive" structure, there is often a modal operator written ♭ that equips the same underlying "set of points" with the "discrete topology".

Narya implements an extension of `Multimodal Type Theory <https://arxiv.org/abs/2011.15021>`_ (MTT), which is a general framework for describing type theories equipped with modal operators.  It is parametrized by a *mode theory*, which specifies not only the modal operators, but also the classes of types they can be applied to and their relationships.

The basic ingredient of a mode theory is a 2-category.  Its objects are called *modes*, and specify the "classes of types" that exist in the theory:  each mode has its own separate ordinary type theory.  In Narya, the name of a mode is the same as the name of the *universe* whose elements are types at that mode.  In particular, the usual universe name ``Type`` is actually the name of the unique mode of the default trivial mode theory (as well as the mode of most single-moded theories).

The morphisms of the mode theory are called *modalities*: each may induce a modal operator that is a functor mapping types of its source mode to types of its target mode.  Finally, the 2-cells of the mode theory specify natural transformations relating the modal operators to each other.

Although Narya supports arbitrary mode theories internally, at present there is no way for the user to specify a mode theory directly: all mode theories have to be coded in OCaml and built in to Narya at compile-time.  This limitation will be overcome in the future, but it is tricky because specifying a mode theory involves not only defining a 2-category but also giving *algorithms* for computing with it, specifically for finding 2-cells and testing whether two composites of 2-cells are equal.

The currently available mode theories are selected by command-line flags, and are summarized in the following table.  (There are also some variants of these, discussed below and particularly in :ref:`Modal parametricity`.)  The default names for the modes and modalities shown in the table can be overridden by additional command-line flags ``-modes`` and ``-modalities``.

.. csv-table:: Mode theories
   :widths: auto
   :header-rows: 1
   :stub-columns: 1

   "Command-line flag", "Modes", "Modalities", "2-cells"
   "``-functor``", "| ``DomType``,
   | ``CodType``", "``○ : DomType → CodType``", "--"
   "``-composed-functors``", "| ``AType``,
   | ``BType``,
   | ``CType``", "| ``○ : AType → BType``,
   | ``▱ : BType → CType``", "--"
   "``-transformation``", "| ``DomMode``,
   | ``CodMode``", "| ``○ : DomMode → CodMode``,
   | ``▱ : DomMode → CodMode``", "| ``α : ○ ⇒ ▱``
   | (locally posetal)"
   "``-composable-transformations``", "| ``DomMode``,
   | ``CodMode``", "| ``○ : DomMode → CodMode``,
   | ``▱ : DomMode → CodMode``,
   | ``▷ : DomMode → CodMode``", "| ``α : ○ ⇒ ▱``,
   | ``β : ▱ ⇒ ▷``,
   | ``βα : ○ ⇒ ▷``
   | (locally posetal)"
   "``-interchange``", "| ``AType``,
   | ``BType``,
   | ``CType``", "| ``▹, ◃ : AType → BType``,
   | ``▸, ◂ : BType → CType``", "| ``α : ▹ ⇒ ◃``,
   | ``β : ▸ ⇒ ◂``,
   | interchange square
   | (locally posetal)"
   "| ``-coreflector``,
   | a.k.a. ``-crisp``", "``Type``", "``♭ : Type → Type``", "| ``♭∘♭ ≅ ♭``, ``♭ ⇒ 1``
   | (locally posetal)"
   "``-reflector``", "``Type``", "``♯ : Type → Type``", "| ``♯∘♯ ≅ ♯``, ``1 ⇒ ♯``
   | (locally posetal)"
   "``-spatial``", "``Type``", "| ``♭ : Type → Type``
   | ``♯ : Type → Type``", "| ``♭∘♭ ≅ ♭``, ``♭ ⇒ 1``,
   | ``♯∘♯ ≅ ♯``, ``1 ⇒ ♯``,
   | ``♯♭ ≅ ♯``, ``♭♯ ≅ ♭``
   | (locally posetal)"
   "``-cospatial``", "``Type``", "| ``♯ : Type → Type``
   | ``♭ : Type → Type``", "| ``♯∘♯ ≅ ♯``, ``1 ⇒ ♯``,
   | ``♭∘♭ ≅ ♭``, ``♭ ⇒ 1``,
   | ``♯♭ ≅ ♭``, ``♭♯ ≅ ♯``
   | (locally posetal)"
   "``-ambiflector``", "``Type``", "``♮ : Type → Type``", "| ``♮ ⊣ ♮``, ``♮∘♮ ≅ ♮``,
   | ``1 ⇒ ♮``, ``♮ ⇒ 1``,
   | ``♮♮ ≅ ♮``, ``♮ ⊣ ♮``"
   "``-adjunction``", "``Disc``, ``Type``", "| ``△ : Disc → Type``,
   | ``□ : Type → Disc``", "``△ ⊣ □``"
   "``-coreflection``", "``Disc``, ``Type``", "| ``△ : Disc → Type``,
   | ``□ : Type → Disc``", "| ``△ ⊣ □`` with
   | ``△□ ⇒ 1`` and ``□△ ≅ 1``
   | (locally posetal)"
   "``-local``", "``Disc``, ``Type``", "| ``△ : Disc → Type``,
   | ``□ : Type → Disc``
   | ``∇ : Disc → Type``", "| ``△ ⊣ □ ⊣ ∇`` with
   | ``△□ ⇒ 1``, ``1 ≅ □△``,
   | ``1 ⇒ ∇□``, and ``□∇ ≅ 1``
   | (locally posetal)"
   "``-tconn``", "``Disc``, ``Type``", "| ``◇ : Type → Disc``,
   | ``△ : Disc → Type``,
   | ``□ : Type → Disc``", "| ``◇ ⊣ △ ⊣ □`` with
   | ``△□ ⇒ 1``, ``1 ≅ □△``,
   | ``1 ⇒ △◇``, ``◇△ ≅ 1``
   | (locally posetal)"
   "``-gwpt``", "``Disc``, ``Type``", "| ``△ : Disc → Type``,
   | ``□ : Type → Disc``,
   | ``◇ : Type → Disc``,
   | ``∇ : Disc → Type``", "| ``△ ⊣ □`` and ``◇ ⊣ ∇``
   | with ``◇∇ ≅ 1``,
   | ``◇△ ≅ 1``, and ``□∇ ≅ 1``"
   "``-ambiflection``", "``Disc``, ``Type``", "| ``△ : Disc → Type``,
   | ``□ : Type → Disc``", "| ``△ ⊣ □`` and ``□ ⊣ △`` with
   | ``□△ ≅ 1``, ``1 ⇒ △□``, ``△□ ⇒ 1``"

Just as ordinary dependent type theory has semantics in any (∞-)topos, modal type theory has semantics in any *diagram* of (∞-)toposes indexed by its mode 2-category.  The functors between such toposes are required to preserve finite limits, but in general nothing more.  Thus, the ``-functor`` theory can be interpreted in any finite-limit-preserving functor between toposes, and so on.

On the names for these theories that may not be self-explanatory:

* ``-spatial`` type theory was so-called in the paper `Brouwer's fixed-point theorem in real-cohesive homotopy type theory <https://arxiv.org/abs/1509.07584>`_ because its intended models were toposes of spaces, with ``♭`` assigning the discrete topology and ``♯`` the codiscrete one, and ``♭ ⊣ ♯``.
* ``-cospatial`` is the dual of ``-spatial``, with ``♯ ⊣ ♭`` instead.
* ``-crisp`` type theory was so-called in the paper `Internal Universes in Models of Homotopy Type Theory <https://arxiv.org/abs/1801.07664>`_ because its ``♭``-annotated variables (see below) were called "crisp" variables (taken from the previous paper).
* ``-local`` indicates a "local geometric morphism", which is the name in topos theory for such an adjoint triple of finite-limit-preserving functors between toposes with the outer adjoints ``△`` and ``∇`` fully faithful.  Note that ``△□`` and ``∇□`` are an adjoint pair of a coreflector and a reflector on ``Type``, so this contains ``-spatial`` as a sub-theory.
* ``-tconn`` is short for "totally connected geometric morphism", which is the name in topos theory for such an adjoint triple of finite-limit-preserving functors, with the inner adjoint ``△`` fully faithful.  (The mode theory ``-coreflection`` is also known as a merely *connected* geometric morphism.)  Dually to ``-local``, here ``◇△`` and ``△□`` are an adjoint pair of a reflector and coreflector, so this contains ``-cospatial`` as a sub-theory.
* ``-gwpt`` is short for "geometrically well-pointed topos", meaning a geometric morphism ``△ ⊣ □`` having a section ``◇ ⊣ ∇``, in the category of toposes and geometric morphisms, such that the section is a geometric embedding.
* ``-ambiflector`` is a single functor that is both a reflector and a coreflector, adjoint to itself.
* ``-ambiflection`` is the two-mode analogue of ``-ambiflector``, both a reflection and a coreflection.

The mode ``Disc`` reflects the common feature of many models in which types at that mode have "discrete" topological or higher structure.  One instance of this that can be turned on in Narya is Parametrically :ref:`Discrete modalities`.

Requests for, or contributions of, new mode theories are very welcome.


Modes
^^^^^

As noted above, the name of a mode is the same as the name of its universe of types.  You can override the above defaults with the ``-modes`` command-line flag, which should be passed a comma-separated list of names to be used in place of the defaults, in the order listed above for each mode theory.

Because universes are types, their names inhabit the same name domain as keywords and constant names.  But they are not namespaced, and take precedence over user-defined constants.  For instance, you cannot define a constant named ``Type`` unless you have renamed that mode.

In general, the mode of a compound type or term is deduced automatically from those of its components.  It may occasionally happen that Narya is unable to do this and will report an error; in that case you can add an explicit ascription such as ``: Type`` (this is one rare situation in which you may want to write ``a : A : Type``, although ``a : (A : Type)`` is still easier to read).


Modalities
^^^^^^^^^^

For technical reasons, the underlying category of a mode theory 2-category in Narya is always a *freely generated* category (such a 2-category is called *flexible* or *cofibrant*).  Thus, each mode theory specifies a "directed multigraph" or "quiver", whose vertices are the modes and whose edges are *generating modalities*.  General modalities are then free composites of generating ones.  (The identity modality at each mode is, of course, the composite of zero generators.)

Each generating modality has a name, which must be a valid identifier but belongs to a separate name domain from keywords and user constants.  Thus, there can be both a modality named ``♭`` and a constant named ``♭``.  In fact, this sort of "punning" is actually recommended, with the constant ``♭`` being the internalized modal operator (see :ref:`Modal datatypes` and :ref:`Modal records and codata`) induced by the modality ``♭``.  You can override the above default names for modalities with the ``-modalities`` command-line flag, which should be passed a comma-separated list of names to be used in place of the defaults, in the order listed above for each mode theory.

Composite modalities are named by a space-separated sequence of generators, in "applicative order": if ``μ`` is a modality from mode ``p`` to mode ``q``, and ``ν`` is a modality from mode ``q`` to mode ``r``, then ``ν μ`` is the composite modality from mode ``p`` to mode ``r``.  In addition, if *all* the modalities in a mode theory have single-unicode-character names (as is the case for all the defaults above), then they can be written without spaces in between, for instance ``△□`` in the coreflection theory.

The freeness of the category of modalities is not a semantically significant restriction, because every 2-category is *equivalent* to one whose underlying 1-category is free (known as its "strictification" or "cofibrant replacement").  Thus, for example, the mode theory ``-coreflector`` has one generating modality ``♭``, which induces many other modalities such as ``♭♭`` and ``♭♭♭``, but all of these are *isomorphic* to ``♭`` by modal 2-cells.

The only place that modality names appear in code is as *annotations*, which are written as

.. code-block:: none

   (x :μ| A)

Such annotations appear as the domains of :ref:`Modal function-types`, as the arguments of constructors of :ref:`Modal datatypes`, as discriminees in :ref:`Windowed matches`, and as self-variables and projection heads for :ref:`Modal records and codata`.  Since modality names are required to be valid identifiers, they are lexed separately from the symbols ``:`` and ``|``, so no spaces are required in ``:μ|`` no matter what the name of ``μ``.  However, if the modality is a composite and not all modality names are single characters, then spaces are required between the generators.

In addition, a mode theory can mark some modalities as having further properties, which will be discussed below in appropriate sections.

* A *tangible* modality can appear in the domain of :ref:`Modal function-types` and the arguments of constructors of :ref:`Modal datatypes`.
* A *pellucid* modality can appear as the window in :ref:`Windowed matches`.
* A *transparent* modality can appear as the window in :ref:`Windowed matches` against non-recursive datatypes.
* A *translucent* modality can appear as the window in :ref:`Windowed matches` against non-recursive datatypes with only one constructor.
* A *sinister* modality must be a left adjoint in the mode theory, and can appear on the self variable of :ref:`Modal records and codata`.
* A *discrete* modality trivializes parametricity on its image; see :ref:`Discrete modalities`.


Modal cells
^^^^^^^^^^^

There is not yet a syntax for printing and referring to modal cells.  Thus, although internally Narya supports arbitrary (cofibrant) 2-categories as mode theories, at present a 2-cell can only be used when it is uniquely determined.  Each mode theory supplies an algorithm for finding such 2-cells automatically whenever needed.  Many of the supplied mode theories are *locally posetal*, meaning that any two parallel 2-cells are equal and so any extant 2-cells can always be found uniquely.


Modal contexts
--------------

Using modal type theory requires a bit more attention to "contexts" than using ordinary type theory.  The *context* of a term is what would be displayed above the line if you replace that term by a :ref:`hole <Holes>` and display the hole: it lists all the variables that are in scope at that point.  In modal type theory, every context has a mode, which is the same as the mode of the term being defined in that context (and its type).  Modal type theory additionally extends the notion of context in two ways: locks and annotations.

* If ``μ`` is a modality from mode ``p`` to mode ``q``, then a context at mode ``q`` can be *locked* by ``μ`` to produce a context at mode ``p``.
* Every variable in a context is *annotated* by some modality whose target is the mode of the context.  A variable of type ``A`` annotated by ``μ`` is denoted ``x :μ| A``.  If ``μ`` is a modality from mode ``p`` to mode ``q``, so that the context has mode ``q``, then the type ``A`` has mode ``p``, and is defined in a context consisting of the previous variables that is *locked* by ``μ`` to make it be at mode ``p``.

Semantically, a variable ``x :μ| A`` is equivalent to a variable belonging to ``μ A``, meaning the modal operator associated to ``μ`` applied to ``A``.  But syntactically, modally annotated variables are more primitive, with modal operators being characterized by a universal property that refers to modal variables and context locks.  The semantic meaning of a context lock is a "left adjoint" to the modal operator.

Annotations and locks interact by way of *key* 2-cells: when a variable in a context is accessed, there must be a key 2-cell from its annotation to the composite of all locks to its --- hence, in particular, those two modalities must have the same source (they always have the some target).  In general, the user must specify the 2-cell to use, but since Narya has no syntax for 2-cells yet, the key is inserted automatically when it is unique (in a locally posetal mode theory, this is the case whenever it exists).  But if no such key exists (or if it is not unique), the variable remains locked and cannot be used.

When displaying a context, such as the context of a hole, variable annotations are printed ``x :μ| A`` as above, while each variable that is behind nonidentity locks is shown as locked by the composite of those locks.  Thus, you can see immediately what sort of key 2-cell would be required to use that variable.  Ordinary variables ``x : A`` are simply those annotated by an identity modality.


Modal function-types
--------------------

Since the only :ref:`Built-in types` are universes and functions, in modal type theory we must make both of these modally-aware.  As mentioned in :ref:`Modes`, each mode induces an eponymous universe type.  For functions, we have a *modal function-type* written

.. code-block:: none

   (x :μ| A) → B

In this syntax:

* ``μ`` is a modality (perhaps a generating one or a composite of generators) from some mode ``p`` to some mode ``q``.  To be used this way, the modality ``μ`` must be *tangible*.  (In most mode theories, most or all modalities are tangible.)
* ``A`` is a type at mode ``p``, defined in the current context :ref:`locked <Modal contexts>` by ``μ``.
* ``B`` is a type at mode ``q`` defined in the current context extended by a variable ``x`` of type ``A`` that is :ref:`annotated by <Modal contexts>` ``μ``.

The entire expression ``(x :μ| A) → B`` is then a type at mode ``q``.  And since parameters of a definition are really just function arguments, the same syntax can be used for them:

.. code-block:: none

   def foo (x :μ| A) : B ≔ ...

Elements of the type ``(x :μ| A) → B``, called *modal functions*, are defined by abstraction and used by application, like ordinary functions.  However:

* In an application ``f a`` where ``f : (x :μ| A) → B``, the argument ``a`` is typechecked in the current context locked by ``μ``.
* In an abstraction ``(x ↦ M) : (x :μ| A) → B``, the body ``M`` is typechecked in the current context extended by a variable ``x`` of type ``A`` annotated by ``μ``.

Semantically, a modal function in ``(x :μ| A) → B`` is equivalent to a function ``(x : μ A) → B`` where ``μ A`` denotes application of the modal operator associated to the modality ``μ``.  However, syntactically modal functions are, in a sense, more basic, with the modal operator determined by a universal property using modal functions.

In general, higher-dimensional versions of modal function-types behave like those of ordinary function-types.  For instance, if ``f : (x :μ| A) → B`` then

.. code-block:: none

   refl f : {x₀ :μ| A} {x₁ :μ| A} (x₂ :μ| Id A x₀ x₁) → Id B (f x₀) (f x₁)

For the exception, see :ref:`Discrete modalities`.


Modal datatypes
---------------

The semantic equivalence between ``(x :μ| A) → B`` and ``(x : μ A) → B`` suggests that ``μ A`` is characterized by a positive universal property, making it similar to a :ref:`datatype <Inductive datatypes and matching>`.  Taking this seriously, Narya allows the definition of arbitrary *modal datatypes*, of which positive modal operators are a simple special case.

Modal constructors
^^^^^^^^^^^^^^^^^^

Any argument of any constructor of any datatype can be modally annotated, as with the domain of a modal function.  (As in that case, the modality must be tangible.)  A modal operator is then the particular case of a single-argument single-constructor datatype (which is trivial if not modally annotated).  For instance, the functor operator in the ``-functor`` mode theory can be defined by

.. code-block:: none

   def ○ (A :○| DomType) : CodType ≔ data [ circ. (x :○| A) ]

Note that the type ``A`` must be a modal variable, so that it can be accessed behind the lock induced by the annotation in the argument.

The constructor ``circ.`` then behaves like a modal function ``(x :○| A) → ○ A``.  And we can match against an element of ``○ A``, obtaining a modal variable:

.. code-block:: none

  def foo (A :○| DomType) (u : ○ A) : B ≔ match u [ circ. x ↦ ? ]
  
Here in the hole we have a variable ``x :○| A``.  This says essentially that ``circ. : (x :○| A) → ○ A`` is the "universal modal function" with its domain.

In general, higher-dimensional versions of modal datatypes behave like those of ordinary datatypes.  For instance, we have

.. code-block:: none

   Id ○ : {A₀ :○| DomType} {A₁ :○| DomType} (A₂ :○| Id DomType A₀ A₁)
            →⁽ᵉ⁾ Id CodType (○ A₀) (○ A₁)

and ``Id ○ A₂`` behaves like an indexed datatype ``○ A₀ → ○ A₁ → CodType`` with a single constructor

.. code-block:: none

   circ. {x₀ :○| A₀} {x₁ :○| A₁} (x₂ :○| A₂ x₀ x₁) : Id ○ A₂ (circ. x₀) (circ. x₁)

For the exception, see :ref:`Discrete modalities`.


Windowed matches
^^^^^^^^^^^^^^^^

Ordinary matches on modal datatypes, however, are insufficient in general to prove basic facts like the functoriality of modal operators.  For instance, in the ``-composed-functors`` mode theory, if we define modal operators for both generating modalities and their composite:

.. code-block:: none

   def ○ (X :○| AType) : BType ≔ data [ circ. (_ :○| X) ]

   def ▱ (Y :▱| BType) : CType ≔ data [ par. (_ :▱| Y) ]

   def ▱○ (X :▱○| AType) : CType ≔ data [ parcirc. (_ :▱○| X) ]

then we can define a transformation from ``▱○ X`` to ``▱ (○ X)``:

.. code-block:: none

   def colax (X :▱○| AType) (u : ▱○ X) : ▱ (○ X) ≔ match u [
   | parcirc. x ↦ par. (circ. x)]

but attempting to define a transformation the other way runs into a problem.  We start with the obvious

.. code-block:: none

   def lax (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
   | par. y ↦ ? ]

We would now like to match on ``y``, destructing it into ``circ. x``, and return ``parcirc. x``.  But in the hole context we have ``y :▱| ○ X``, and in fact ``y`` doesn't even live at the mode ``CType`` where we are working, so an ordinary ``match y`` is impossible.

In MTT this problem is solved by *window modalities*.  The discriminee of a match can be annotated by a modality, called a "window modality".  In this case it is checked or synthesized in a context locked by that window modality, and the window modality is composed with any annotations on the pattern variables in the baranches of the resulting match (to put them at the correct mode).

In particular, in the above case we can write

.. code-block:: none

   def lax (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
   | par. y ↦ match (y :▱| _) [ circ. x ↦ ? ]]

The placeholder ``_`` stands for the datatype that ``y`` belongs to, which can be used instead if desired:

.. code-block:: none

   def lax (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
   | par. y ↦ match (y :▱| ○ X) [ circ. x ↦ ? ]]

Now in the hole we have ``x :▱○| X``, annotated by the composite modality ``▱○``, so we can fill the hole with ``parcirc. x`` as desired.

.. code-block:: none

   def lax (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
   | par. y ↦ match (y :▱| _) [ circ. x ↦ parcirc. x ]]

In general, the correct window modality for a match cannot be deduced automatically, and must be supplied by the user with an annotation of this sort.  However, there is one case in which a window modality is inferred automatically: if the term being matched against is a free variable with a modal annotation on it, then it obviously needs *some* window modality, and the obvious choice is the same one as its annotation.  This is the case in the example of ``lax`` above, so we can also write

.. code-block:: none

   def lax (X :▱○| AType) (u : ▱ (○ X)) : ▱○ X ≔ match u [
   | par. y ↦ match y [ circ. x ↦ parcirc. x ]]

Note, though, that even for a variable this is not always the *correct* choice: you might want to use a different window modality that's related to the variable's annotation by a key, in which case the window needs to be given explicitly.

In principle, a window modality can be applied to *any* match: the datatype doesn't have to have any modal constructors itself.  However, this has consequences for the semantics of the window modality: it necessarily "preserves" all datatypes that it can be a window for.  Since this may be undesired, Narya allows a mode theory to specify three levels of "transparency" for modalities governing their applicability as windows.  (These are unrelated to the similarly-named :ref:`attributes of record types <Eta-expansion and opacity>`.)

* A *pellucid* modality can be a window for any match at all.  This is a very strong property: it implies, for instance, that the modal operator preserves recursive datatypes such as the natural numbers.  The only nonidentity pellucid modality in the standard mode theories is ``△`` in ``-tconn``; this is semantically justified because it is the inverse image of a locally connected geometric morphism, so it preserves both colimits and function-types, out of which inductive types are constructed (at least in Grothendieck topoi) by transfinite iteration.  (Some additional modalities are pellucid in :ref:`discrete mode theories <Modal parametricity>`.)

* A *transparent* modality can be a window for a match on any *non-recursive* datatype.  This means that the modal operator preserves finite colimits (or, at least, finite coproducts; other finite colimits must wait for :ref:`Higher inductive types`).  Since left adjoints preserve colimits, all the left adjoints in the standard mode theories are transparent:

  - ``△`` in ``-adjunction`` and ``-coreflection``
  - ``♭`` in ``-spatial``
  - ``♯`` in ``-cospatial``
  - ``△``, ``□``, and ``△□`` in ``-local``
  - ``△``, ``◇``, and ``△◇`` in ``-tconn`` and ``-gwpt``
  - ``♮`` in ``-ambiflector``
  - ``△``, ``□``, and ``△□`` in ``-ambiflection``

  In addition, there is a variant of ``-functor`` called ``-transparent-functor`` that makes the modality ``○`` transparent.

* A *translucent* modality can be a window for a match on any *non-recursive single-constructor* datatype.  This is the minimum necessary to ensure we can prove functoriality of modal operators, as above.  All the modalities in the standard mode theories are translucent (though some in :ref:`discrete mode theories <Modal parametricity>` are not).

A translucent modality can also be a window for *indexed* single-constructor non-recursive datatypes, which in particular means it preserves the Martin-Löf identity type, and therefore preserves finite limits internally.  However, even a non-translucent modality preserves finite products, and in the standard categorical semantics it must preserve at least pullbacks of display maps.  Moreover, when :ref:`Higher Observational Type Theory` is on, all modal operators preserve the observational identity types; this follows from the remarks above about higher-dimensional versions of modal datatypes.  Thus, one should really think of *all* modal operators as semantically corresponding to *finite-limit-preserving* functors.  (This is particularly convenient for applications to topos theory, in which a geometric morphism is an adjoint pair of finite-limit-preserving functors.)


Modal records and codata
------------------------

The "positive" modal operators obtained as a special case of modal datatypes are the only ones present in the original theory MTT.  Narya also implements an enhancement called `Multimodal Adjoint Type Theory <https://entics.episciences.org/paper/view/id/12300>`_ (based on an earlier paper on `Modalities and Parametric Adjoints <https://dl.acm.org/doi/10.1145/3514241>`_) that adds "negative" modal operators, which are a special case of *modal records and codatatypes*.

Dually to modal constructors of datatypes, any record or codatatype can have *modal fields*.  And just as a modal constructor can be viewed as a modal function, so can a modal field.  But now since the domain of a field-qua-function is the record/codata type itself, that is what gets modally annotated.

For technical reasons, the modality which is used in such an annotation is required to have a right adjoint (that is, to be a left adjoint) in the mode 2-category.  Each mode theory can mark some of its modalities as *sinister* by supplying a right adjoint to them; they can then annotate modal fields.  The sinister modalities in the standard mode theories are the same as the transparent ones:

  - ``△`` in ``-adjunction`` and ``-coreflection``
  - ``♭`` in ``-spatial``
  - ``♯`` in ``-cospatial``
  - ``△``, ``□``, and ``△□`` in ``-local``
  - ``△``, ``◇``, and ``△◇`` in ``-tconn`` and ``-gwpt``
  - ``♮`` in ``-ambiflector``
  - ``△``, ``□``, and ``△□`` in ``-ambiflection``

The simplest sort of modal codatatype has one field that is modally annotated.  For instance, in the mode theory ``-coreflection`` we have

.. code-block:: none

   def □ (A :□| Type) : Disc ≔ codata [
   | (x :△| _) .unbox : A ]

The placeholder ``_`` stands for the codatatype being defined, which can be used instead if desired:

.. code-block:: none

   def □ (A :□| Type) : Disc ≔ codata [
   | (x :△| □ A) .unbox : A ]

Note that the ``△``-annotation appears on the self-variable ``x`` to which the field ``.unbox`` is applied.  We have named the modal operator ``□``, the right adjoint of ``△``, because it goes in that direction, and indeed is equivalent to the positive modal operator associated to ``□``.  Thus, the modal operators that can be defined negatively in the supplied mode theories are the right adjoints:

  - ``♯`` in ``-spatial``
  - ``♭`` in ``-cospatial``
  - ``□`` in ``-adjunction`` and ``-coreflection``
  - ``△``, ``□``, and ``△□`` in ``-tconn``
  - ``□``, ``∇``, and ``∇□`` in ``-local`` and ``-gwpt``
  - ``♮`` in ``-ambiflector``
  - ``△``, ``□``, and ``△□`` in ``-ambiflection``

Note also that ``A`` itself is ``□``-annotated and lives at the mode ``Type``, the domain of ``□``.  In general, the type of a modal field is typechecked in a context locked by the *right adjoint*, which in the above case is ``□`` so that we can use the ``□``-annotated variable ``A``.

Similarly, when defining an element of a modal codatatype by comatching, the value corresponding to a modal field is typechecked in a context locked by the right adjoint:

.. code-block:: none

   def box (A :□| Type) (a :□| A) : □ A ≔ [
   | .unbox ↦ a ]

When *projecting* a modal field from an element of a modal datatype, however, the element is typechecked in a context locked by the *left* adjoint.  Unfortunately, Narya can't infer this modality from the field name, because the same field name could be used by many different codatatypes with different modal annotations: the only way to find the correct codatatype is to synthesize a type for the element being projected, but that can't be done until we already have the modality to lock the context to synthesize it in!  Therefore, the element being projected must be explicitly annotated with that left adjoint modality, mirroring the self variable in the codata definition.

.. code-block:: none

   def unbox (A :△□| Type) (u :△| □ A) : A ≔ (u :△| _) .unbox

Once again, you can also write ``(u :△| □ A) .unbox`` if desired.

The unit and counit of the adjunction ``△ ⊣ □`` are used in the reduction and equality-checking rules.  For instance, with the above definitions, in context of ``A :△□| Type`` and ``a :△□| A`` we can write ``unbox A (box A a)``, which then reduces to ``a`` but with the counit cell ``△□ ⇒ 1`` applied as a key.

The unit cell isn't used for modal codatatypes, but it is used for modal record types which have an η-conversion rule.  To have modal fields, a record must be defined using :ref:`self variables <Self variables for record types>`:

.. code-block:: none

   def □′ (A :□| Type) : Disc ≔ sig (
     (x :△| _) .unbox : A)

Then we can define

.. code-block:: none

   def box_unbox (A :□| Type) (u : □′ A) : □′ A ≔
     (unbox ≔ (u :△| _) .unbox)

This doesn't reduce, but it should be equal to ``u`` by η-conversion.  However, to test records for η-equality we need to project out all their fields, and in order to write ``(box_unbox A u :△| _) .unbox`` and ``(u :△| _) .unbox`` we need them to be defined in a ``△``-locked context.  Thus, internally Narya applies the unit ``1 ⇒ □△`` as a key first, obtaining both ``box_unbox A u`` and ``u`` in a context locked by ``□△``, then projects out the ``.unbox`` field and compares the results for equality in the remaining ``□``-locked context.  (As a user you shouldn't often need to be aware of this, but we mention it to justify the requirement of a full adjunction.)

In general, higher-dimensional versions of modal records and codata behave like those of ordinary records and codata.  For instance, we have

.. code-block:: none

   Id □′ : {A₀ :□| Type} {A₁ :□| Type} (A₂ :□| Id Type A₀ A₁) → Id Disc (□′ A₀) (□′ A₁)

and ``Id □′ A₂`` behaves like a record type with a single field

.. code-block:: none

   (u :△| Id □′ A₂ u₀ u₁) .unbox : A₂ ((u₀ :△| □′ A₀) .unbox) ((u₁ :△| □′ A₁) .unbox)

As before, for the exception see :ref:`Discrete modalities`.

Currently, :ref:`higher fields <Higher coinductive types>` cannot also be modal.
