External parametricity
======================

The type of parametricity described in :ref:`Parametricity` is *internal parametricity*, meaning that the operations such as ``rel`` and ``Br`` and ``⁽ᵖ⁾`` are ordinary operations inside type theory that can be applied to any types or terms in any context.  This is a powerful tool; for instance, it can be used to prove that the naïve Church natural numbers ``(X : Type) → X → (X → X) → X`` in fact have the full dependent induction principle of ``ℕ``, or that the polymorphic identity function is the only inhabitant of its type (here we assume ``-arity 1``):

.. code-block:: none

   def pid (f : (X : Type) → X → X) (A : Type) (a : A) : eq A a (f A a) ≔
     rel f (Gel A (eq A a)) {a} (rfl.,) .ungel

(Results such as this are related to the origin of the term "parametricity": the idea is that any such ``f`` must be defined "parametrically" in the type ``X``.)

However, the flip side of that power is that it limits the additional axioms that can be assumed.  For instance, internal parametricity is inconsistent with classical axioms such as the Law of Excluded Middle, since they could be used to define other elements of ``(X : Type) → X → X`` by dividing into cases based on, for instance, whether ``X`` is isomorphic to ``Bool``.  Or more directly to derive a contradiction:

.. code-block:: none

   def oops (LEM : (X : Type) → X + ¬ X) : ⊥
     ≔ match LEM⁽ᵖ⁾ (Gel ⊤ (_ ↦ ⊥)) [
   | inl. x ⤇ x.1 .ungel
   | inr. x ⤇ x.0 ()]

Global parametricity
--------------------

Historically prior to internal parametricity was *external* parametricity, in which operations such as ``⁽ᵖ⁾`` are meta-theoretic *operations on syntax*.  In particular, they can be applied only to *closed* terms and types (those defined in the empty context).  Of course, an object defined in a nonempty context can be abstracted over that context to produce a closed one, for instance a term ``b(x) : B`` defined in the context of a variable ``x : A`` can be abstracted into

.. code-block:: none

   x ↦ b(x) : A → B

But applying parametricity to this then changes the (abstracted) context, as we have seen:

.. code-block:: none

   (x ↦ b(x))⁽ᵖ⁾ : {a₀ : A} {a₁ : A} (a₂ : Br A x₀ x₁) →⁽ᵖ⁾ Br B (b(a₀)) (b(a))

Put differently, the external parametricity operations could also be applied in any context, but they would then degenerate the context like passing into a :ref:`higher field <Higher coinductive types>`.

The flag ``-external`` switches Narya's parametricity from internal to external.  To first approximation, this change means simply that the parametricity operations such as ``rel`` and ``Br`` and ``⁽ᵖ⁾`` can only be applied to closed terms (you must abstract over the context yourself).  For instance, we can compute the bridges of any specific defined type, such as the type ``ℕ`` of natural numbers or the type ``Group`` of groups, but we can't compute the bridges of an assumed *variable* type, or the ``rel`` of an assumed variable.  This blocks proofs such as the uniqueness of polymorphic identity above, in which we must apply ``rel`` to the assumed variable ``f``.

Since the parametricity operations also compute fully *on* closed terms (at least in the "up-to-definitional-isomorphism" sense), we can then more or less think of them as meta-operations on syntax, in line with the original meaning of external parametricity.  However, since parametricity of a closed term is *another* closed term, we can still iterate the parametricity translation, computing higher-dimensional bridges of closed types and their elements, and symmetries such as ``sym`` are still available on these higher-dimensional objects.

Modally guarded parametricity
-----------------------------

In fact, Narya's ``-external`` flag is a little more permissive than this.  Following in the footsteps of :ref:`Displayed type theory`, Narya requires ``-external`` to be specified along with a suitable mode theory, and it then allows the parametricity operations to be applied to any suitably *modal* term, in other words a term defined in a suitably locked context.  The modality used for this is listed in the "Param. Locker" column in the table at :ref:`Modal parametric discrenesess`.  (Mode theories without an entry in that column are incompatible with ``-external``; note that some also have arity restrictions, which will be explained under :ref:`semantics <Semantics of modal parametricity>`.)  Thus, for instance, under ``-external -adjunction`` we can compute bridges of any ``△□``-modal object.

Intuitively, the parametric locker modalities allow us to "internalize the metatheory" to a certain degree and write things like "for any closed type ``X``" inside the theory as ``(X :△□| Type)``.  Note that this is different from "for any discrete type ``X``", i.e. ``(X :△| Disc)``: a discrete type *has no* higher-dimensional structure; while a closed type *has* higher-dimensional structure which we can access because it is defined in a context of only other closed and discrete types.  It's potentially confusing because ``△□`` is declared as a "discrete modality", but this means that types of the form ``△□ A`` are discrete, whereas ``X`` in ``(X :△□| Type)`` is rather (semantically) an *element of* such a type, namely ``△□ Type``.

For example, in external parametricity we can prove that the polymorphic identity is the only "closed" element of its type (again under ``-arity 1``):

.. code-block:: none

   def pid (f :△□| (X : Type) → X → X) (A : Type) (a : A) : eq A a (f A a) ≔
     rel f (Gel A (eq A a)) {a} (rfl.,) .ungel

We are then free to assume things such as excluded middle, at least as local hypotheses of another theorem:

.. code-block:: none

   def my_theorem (LEM : (X : Type) → X + ¬ X) ...

Although we can then use ``LEM`` to define exotic elements of ``(X : Type) → X → X``, we will not be able to apply ``pid`` to such an element, since in the ``△□``-locked context of the first argument of ``pid`` the ordinary variable ``LEM`` is not available.  Nor will we be able to derive a contradiction from ``LEM`` in a more direct way, since we cannot write ``LEM⁽ᵖ⁾``.

Modal axioms
------------

Of course, if we want to prove a lot of theorems using excluded middle, it is tedious to assume it explicitly as a hypothesis of every one.  One solution would be to assume it as a "section variable", but such things have not been implemented in Narya yet.  A blunt alternative is to assert it globally as an ``axiom``, but this requires some modification since an axiom *can* have parametricity operations applied to it even under ``-external``.

Another option is to assert the axiom under a suitable modality, such as ``△◇`` in ``-discrete-tconn``:

.. code-block:: none

   axiom LEM : △◇ ((X : Type) → X + ¬ X)

Since ``△◇`` is a discrete modality, although we can write ``LEM⁽ᵖ⁾`` it will now give no information.  To prove a theorem using this form of excluded middle, we have to destruct it into a modal variable, after which we can use it in any ``△◇``-locked context, such as when proving a theorem behind ``△◇``:

.. code-block:: none

   def classical_theorem : △◇ (...) ≔ match LEM [
   | tridia. lem ↦ tridia. ? ]

Now inside this hole, we have ``lem :△◇| (X : Type) → X + ¬ X`` locked by ``△◇``, and hence usable.  But if we ever apply a parametricity operation, the context will get further locked by ``△□``, and since ``△◇△□ = △□`` and there is no key 2-cell ``△◇ ⇒ △□``, the variable ``lem`` will no longer be usable inside that degeneracy.

Of course, at this point we have lost most of the simplicity of asserting a global axiom: our classical theorem doesn't take an explicit ``LEM`` argument, but instead it lives under the modality ``△◇`` and must start with a match against ``LEM``.  In particular, whenever such a theorem is *used* it must also be matched against.  Moreover, this approach is less granular: a theorem under ``△◇`` can use *any* axiom asserted under the same modality, with no indication in its type of which axioms it depends on.


Nonparametric axioms (deprecated)
---------------------------------

*Nonparametric axioms were an experimental feature that is now deprecated in favor of the modal treatment discussed above.  We include the old documentation of this feature here for reference, but it will eventually go away along with the feature.*

It is also possible to define a *nonparametric axiom*, which is treated like a variable and thus cannot appear inside of parametricity operations.  To define a nonparametric axiom, use the attribute ``nonparametric``:

.. code-block:: none

   axiom #(nonparametric) LEM : (P : Type) → P ⊔ ¬ P

Other constants that use nonparametric axioms in their types or definitions, hereditarily, must also be nonparametric.  For definitions, this is deduced automatically, while for axioms it must be marked explicitly with ``nonparametric``.  Similarly, if any of the definitions in a mutual block use a nonparametric constant, then all the constants in the mutual block are nonparametric.

When a definition contains :ref:`holes` but does not (yet) use any nonparametric constants, it is considered parametric, and hence can have dimension-changing degeneracies applied to it.  Therefore, if you later try to fill one of those holes with a term that uses a nonparametric constant, an error will be emitted; it is not possible to retroactively set a definition to be nonparametric since it might already have had dimension-changing degeneracies applied to it by other definitions.  In this case, you have to undo back to the original definition and manually copy your desired nonparametric term in place of the hole.


Semantics of modal parametricity
--------------------------------

While the ordinary mode theories described in :ref:`Modal type theory` are intended to be generic, with semantics in any diagram of toposes (or more general categories) of a suitable shape, each of the discrete mode theories listed in :ref:`Modal parametric discreteness` (except for ``-discrete-functor``, which is mainly for testing) has a *specific* intended class of semantic models.  These semantics justify the choices made for the behavior and restrictions of these theories.  Here we sketch these intended models; this is not important for using Narya, but it may be helpful to understand it.

As mentioned in :ref:`Parametricity`, internally parametric Narya has semantics in the topos of *n*-ary semicartesian cubical sets (or spaces, or objects of some other topos ℰ).  Narya's modally-guarded external parametricity similarly has semantics in the topos of *n*-ary semicartesian *semi-cubical* sets, which have faces and symmetries but no degeneracies.  In both cases, the intended semantics of discrete mode theories uses such a topos of (semi-)cubical objects as the interpretation of the mode ``Type``, while the underlying topos of sets (or whatever else) interprets the mode ``Disc``.

In all cases (that is, both internal and external parametricity of all arities) there is a geometric morphism from ``Type`` to ``Disc``.  This consists of an inverse image functor ``△ : Disc → Type``, which produces a constant (semi-)cubical object, and a right adjoint direct image functor ``□ : Type → Disc``, which computes the limit of a (semi-)cubical object regarded as a diagram.  Therefore, we can always use ``-discrete-adjunction``, with ``△`` discrete.

The constant-diagram functor ``△`` also always has a left adjoint that computes the colimit.  This is not, in general, finite-limit-preserving, so it can't be represented by a modality.  However, the existence of this left adjoint does mean that the geometric morphism ``△ ⊣ □`` is locally connected, so that we can mark ``△`` as pellucid.

In the case of *internal* parametricity, the object 0 is initial in the opposite of the cube category (a 0-cube has a unique degeneracy of every dimension).  This implies that the constant diagram functor ``△`` is fully faithful, so the adjunction ``△ ⊣ □`` is a coreflection.  This yields a model of the ``-discrete-coreflection`` mode theory, and we get ``-discrete-coreflector`` by defining ``♭ = △□``, so these theories are applicable to any arity of internal parametricity.

Initiality of 0 also implies that the limit functor ``□`` is just evaluation at 0, so it has a further right adjoint ``∇ : Disc → Type`` that constructs a "coskeletal" cubical set.  Thus, the mode theory ``-discrete-local`` also applies to any arity of internal parametricity, as does ``-discrete-spatial`` where we restrict to the mode ``Type`` with the composites ``♭ = △□`` and ``♯ = ∇□``.

On the other hand, in the case of arity 1 (with or without degeneracies), the object 0 is *terminal* in the opposite of the cube category (every unary cube has exactly one 0-dimensional vertex).  This *also* implies that the constant diagram functor ``△`` is fully faithful, so we can also use ``-discrete-coreflection`` and ``-discrete-coreflector`` for either kind of unary parametricity.

Terminality of 0 does not imply the existence of ``∇``, but it does imply that the *colimit* functor ``◇ : Type → Disc`` left adjoint to ``△`` is evaluation at 0, and hence finite-limit-preserving with a further left adjoint.  Thus, the mode theory ``-discrete-tconn`` is applicable to either kind of *unary* parametricity, as is ``-discrete-cospatial`` if we restrict to the mode ``Type`` with the composites ``♭ = △□`` and ``♯ = △◇``.  Note that in this case both ``♭`` and ``♯`` include ``△``, so both are discrete modalities, unlike the case of ``-discrete-spatial`` where ``♯ = ∇□`` is codiscrete.

In the overlapping case of *unary internal* parametricity, we have ``◇ = □`` and hence ``△ = ∇``, yielding two functors that are adjoint to each other on both sides, so in this case we can use ``-discrete-ambiflector`` with ``♮ = △□ = ∇◇``.

Finally, in the case of *external non-unary* parametricity, there is still an "evaluate at 0" functor, but it is not part of any adjoint string including ``△ ⊣ □``.  But it does have a right adjoint, which we denote ``∇``, and we have ``◇△ = 1``, yielding the ``-discrete-gwpt`` mode theory.  (This is the reason the ``-gwpt`` theory exists: it is the most expressive theory available for external non-unary parametricity.)  It has no single-mode sub-theory because, as noted above, the composite ``∇◇`` cannot be defined directly syntactically: it should be codiscrete rather than discrete, but it has no left adjoint in the mode theory.
