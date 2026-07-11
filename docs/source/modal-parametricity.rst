Modal discreteness
==================

As remarked under :ref:`Modal type theory`, in general modal features and observational higher-dimensional features "commute" past each other without interacting, e.g. the higher-dimensional versions of modal canonical types are again modal canonical types in the same way.  This section describes a special way that modal type theory can interact with parametricity, inspired by `displayed type theory <https://doi.org/10.1017/S096012952510025X>`_, which we call *modal discreteness*.

Modal discreteness requires ``-parametric``, and by default we will assume ``-direction p,rel,Br``.  It also requires choosing a modified mode theory.  The built-in mode theories with discreteness, along with the ordinary mode theory they modify, their restrictions on internal/external parametricity and arity, and their "discrete" modalities and modes (to be explained below), are:

.. csv-table:: Mode theories
   :widths: auto
   :header-rows: 1
   :stub-columns: 1

   "Command-line flag", "Base theory", "Restrictions", "Disc. modalities", "Disc. modes"
   "``-discrete-functor``", "``-functor``", "internal", "``○``", "``DomType``"
   "``-discrete-coreflector``", "``-coreflector``", "| internal
   | or arity 1", "``♭``", "--"
   "``-discrete-spatial``", "``-spatial``", "internal", "``♭``", "--"
   "``-discrete-coreflection``", "``-coreflection``", "| internal
   | or arity 1", "``△``", "``Disc``"
   "``-discrete-local``", "``-local``", "internal", "``△``, ``△□``", "``Disc``"
   "``-discrete-tconn``", "``-tconn``", "arity 1", "``△``, ``△□``, ``△◇``", "``Disc``"

Aside from the first, each of these theories has a specific intended class of semantic models.  As mentioned in :ref:`Semantics of parametricity`, internally parametric Narya has semantics in the topos of *n*-ary semicartesian cubical sets (or spaces, or objects of some other topos ℰ), while externally parametric Narya uses *semi-cubical* objects instead (no degeneracies).  In the intended semantics of the above mode theories with discreteness, such a topos of (semi-)cubical objects is the interpretation of the mode ``Type``, while the underlying topos of sets (or whatever else) interprets the mode ``Disc``.

In all cases (that is, both internal and external parametricity of all arities) there is a geometric morphism from ``Type`` to ``Disc``.  Its inverse image functor ``△ : Disc → Type`` produces a constant (semi-)cubical object, while its direct image functor is the right adjoint ``□ : Type → Disc`` of this, which computes the limit of a (semi-)cubical object regarded as a diagram.  The inverse image also has a left adjoint that computes the colimit, but this is not in general finite-limit-preserving so it can't be represented by a modality.

In the case of *internal* parametricity, the object 0 is initial in the cube category.  This implies that the constant diagram functor is fully faithful, so the adjunction is a coreflection.  This yields the ``-discrete-coreflection`` mode theory, and we get ``-discrete-coreflector`` by defining ``♭ = △□``, so these theories are applicable to any arity of internal parametricity.

Initiality of 0 also implies that the limit functor ``□`` is just evaluation at 0, so it has a further right adjoint ``∇ : Disc → Type`` that constructs a "coskeletal" cubical set.  Thus, the mode theory ``-discrete-local`` also applies to any arity of internal parametricity, as does ``-discrete-spatial`` if we restrict to the mode ``Type`` with the composites ``♭ = △□`` and ``♯ = ∇□``.

On the other hand, in the case of arity 1 (with or without degeneracies), the object 0 is *terminal* in the cube category.  This also implies that the constant diagram functor is fully faithful, so we can also use ``-discrete-coreflection`` and ``-discrete-coreflector`` for either kind of unary parametricity.  Terminality of 0 does not imply the existence of ``∇``, but it does imply that the *colimit* functor ``◇ : Type → Disc`` left adjoint to ``△`` is evaluation at 0, and hence finite-limit-preserving with a further left adjoint.  Thus, the mode theory ``-discrete-tconn`` is applicable to either kind of unary parametricity.

In the overlapping case of *unary internal* parametricity, we have ``◇ = □`` and hence ``△ = ∇``, yielding two functors that are adjoint to each other on both sides.  However, this is no longer a locally posetal mode theory, so it is not yet provided.

In the missing cases of external non-unary parametricity, the "evaluate at 0" functor is not part of any adjoint string including ``△ ⊣ □``, although it does have a right adjoint.  Moreover, ``△`` is not fully faithful in this case, so this mode theory is also not locally posetal, and hence not yet provided.  Thus, ``-external`` can currently only be combined with a discrete mode theory when the arity is 1 (about which, see :ref:`Displayed type theory`).


Discrete modalities
-------------------

To match the semantic idea syntactically, a type is said to be *(parametrically) discrete* if its "bridges are equalities".  In the binary case, this means that ``Br A a₀ a₁`` is equivalent to ``eq A a₀ a₁``, the Martin-Löf identity type that is generated by ``rfl. : eq A a a``, and similarly in higher dimensions.  For other arities, we can similarly assert that ``Br A a₀ a₁`` is equivalent to an "*n*-ary identity type" generated by a single constructor.  For instance, in arity 3 a type is discrete if ``Br A a₀ a₁ a₂`` is equivalent to ``eq3 A a₀ a₁ a₂`` generated by ``rfl. : eq3 A a a a``, and so on.  Remember that semantically, a type is discrete if the *n*-ary cubical diagram of its higher bridges is (equivalent to) a constant functor.

Now, a mode theory can declare any of its *modalities* to be *discrete* (a.k.a. *nonparametric*), which means semantically that all the types in the image of its modal operator are discrete.  Syntactically, however, this is ensured not by an axiom, but by altering the computation rules for modal types involving that modality, essentially building in the elimination rule for ``eq`` wherever there would be a ``Br``.  We will discuss these modified rules below.

In addition to modalities being discrete, a *mode* can also be declared as discrete.  This means that types at that mode have no higher-dimensional versions at all.  For compatibility, it is required that a modality whose source *or* target mode is discrete must also be discrete.


Discrete function-types
-----------------------

If ``○ : DomType → CodType`` is a tangible discrete modality, as in the mode theory ``-discrete-functor``, then ``Br ((x :○| A) → B x) f₀ f₁`` reduces to

.. code-block:: none

   (x :○| A) →⁽ᵖ⁾ Br B x (f₀ x) (f₁ x)

Note that the domain has *not* been degenerated: there is only one variable ``x``, in place of the triple variable we get for a non-discrete modality

.. code-block:: none

   {x₀ :○| A} {x₁ :○| A} (x₂ :○| Br A x₀ x₁) →⁽ᵖ⁾ Br B x₂ (f₀ x₀) (f₁ x₁)

Note that an equivalence between these two types is exactly what we would expect if ``Br A`` is equivalent to ``eq A``.  In addition, in the codomain type ``Br B x (f₀ x) (f₁ x)`` the bridge argument ``x₂`` is replaced by the point argument ``x``; this is well-typed because the same principle applies to ``B : (x :○| A) → CodType``, so that

.. code-block:: none

   Br B : (x :○| A) → Br CodType (B x) (B x)


Discrete datatypes
------------------

The behavior of modal constructors annotated by discrete modalities can be deduced from that of modal function-types, by regarding constructors as functions.  In particular, for the case of a positive modal operator:

.. code-block:: none

   def ○ (A :○| DomType) : CodType ≔ data [ circle. (_ :○| A) ]

we have ``circle. : (_ :○| A) → ○ A``, and therefore for the bridge type we have a constructor

.. code-block:: none

   circle. : (x :○| A) →⁽ᵖ⁾ Br (○ A) (circle. x) (circle. x)

In other words, ``Br (○ A)`` is a datatype indexed by two copies of ``○ A`` with one constructor of this type.  Using this, it's easy to prove that indeed ``Br (○ A) u₀ u₁`` is equivalent to ``eq (○ A) u₀ u₁``, in other words ``○ A`` is discrete as defined above.

Discrete modalities can also be pellucid, transparent, or translucent.  However, a discrete modality cannot currently be used as a window modality for a match against a higher-dimensional datatype.  This is not a semantic restriction, but a limitation of the structure of contexts in Narya; it would be possible to work around but we haven't done it yet.


Codiscrete records and codata
-----------------------------

Similarly, the behavior of modal fields annotated by discrete sinister modalities can be deduced from that of modal function-types by regarding field projections as functions, although there are a few twists.  Consider the negative modal operator in the ``-discrete-spatial`` mode theory:

.. code-block:: none

   def ♯ (A : Type) : Type ≔ sig ( (_ :♭| _) .unsharp : A )

Here the ``.unsharp`` projection can be considered a modal function of type ``(_ :♭| ♯ A) → A``.  Therefore, passing to bridges we see that its degenerate version has type

.. code-block:: none

   (x :♭| ♯ A) →⁽ᵖ⁾ Br A ((x :♭| ♯ A) .unsharp) ((x :♭| ♯ A) .unsharp)

However, this is nothing but ``x ↦ rel ((x :♭| ♯ A) .unsharp)``.  In particular, it *does not contain* ``Br (♯ A)`` anywhere in its domain, and therefore it *does not induce a field* of ``Br (♯ A)``.  That is, fields annotated by discrete modalities *vanish* when passing to higher-dimensional versions of a record or codatatype.

In the particular case of a negative modal operator such as ``♯`` where the *only* field is modal, this means that ``Br (♯ A) u₀ u₁`` has *zero* fields, and therefore it is equivalent to the unit type ``⊤``.  That is, ``♯ A`` is *codiscrete*, the dual of discrete: all of its bridge-types are contractible (uniquely inhabited).  Similarly, ``∇ A`` is codiscrete in the ``-discrete-local`` mode theory, because ``□`` is discrete (as it has a discrete target ``Disc``).

There is no direct way to declare a modality to "be codiscrete": codiscreteness only arises for right adjoints of discrete sinister modalities.  But a codiscrete modality cannot commute with parametricity either, nor can it be discrete (unless the arity is 1, in which case discreteness and codiscreteness coincide).  Thus, the modalities ``♯`` in ``-discrete-spatial`` and ``∇`` in ``-discrete-local`` are declared to be *intangible*, so that they do not admit positive modal operators or appear in modal function-types at all, as there is no consistent way to give behavior for such types.

If a modality is neither tangible nor sinister, like ``♯`` and ``∇``, then that it cannot appear in function-types, datatypes, or record/codatatypes.  Thus, whether or not it is discrete is undetectable to the theory.
