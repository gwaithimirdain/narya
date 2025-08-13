Observational higher dimensions
===============================

There are many ways in which a type theory can be "higher-dimensional", by which we include homotopy type theory (specifically, Higher Observational Type Theory, a.k.a. HOTT), internally parametric type theories, and `displayed type theory <https://arxiv.org/abs/2311.18781>`_.  The internal architecture of Narya is set up to eventually permit the user to mix and match multiple such "directions" of higher-dimensionality, but currently this is not realized.  At the moment, there is only one built-in direction, although its behavior can be customized to any of the above-mentioned theories.

In this section we describe the common features of all these theories; more details will be discussed under :ref:`Parametricity` and :ref:`Higher Observational Type Theory`.  We use the notation of HOTT.


Observational primitives
------------------------

The fundamental aspect of all these higher-dimensional type theories is that each type comes with a specified type family indexed by some copies of itself.  By default, this type family is called ``Id`` (intended to suggest the identity type of HOTT) and depends on two copies of the base type.  That is, for any type ``A`` and two elements ``x:A`` and ``y:A`` we have a type ``Id A x y``.  Under internal parametricity these types are more precisely called *bridge* types, but in this section we will refer to them as identity types and denote them by ``Id``.

Until we get to :ref:`Higher Observational Type Theory` these types do not have all the structure of equality; in particular they are missing *symmetry* and *transitivity*.  However, they do always have *reflexivity*: any element ``x:A`` gives rise to ``refl x : Id A x x``.

Specifically, if ``x`` synthesizes a type ``A``, then ``refl x`` synthesizes ``Id A x x``.  Whereas ``refl x`` can always check against a type of the form ``Id A x x`` in which case it suffices for ``x`` to check against ``A``.  In fact, since the type ``Id A x x`` determines not only the type ``A`` but the element ``x``, in a checking context you can even write ``refl _`` and the element will be inferred.

In addition to reflexivity, these "identity types" types satisfy *congruence*, which is to say that every function preserves them.  Specifically, given ``f : A → B`` and ``a₂ : Id A a₀ a₁``, we have

.. code-block:: none

   ap f a₂ : Id B (f a₀) (f a₁)

The notation ``ap`` for this is traditional in homotopy type theory, standing for "apply" or "action on paths", so it is Narya's default; but as we will see later it can be customized.  This also works for curried multi-argument functions: if ``g : A → B → C`` and ``a₂ : Id A a₀ a₁`` and ``b₂ : Id B b₀ b₁`` we have

.. code-block:: none

   ap g a₂ b₂ : Id C (g a₀ b₀) (g a₁ b₁)

In this syntax, the function ``f`` or ``g`` can be a non-synthesizing abstraction such as ``x ↦ …``, but the arguments such as ``a₂`` and ``b₂`` must synthesize (an appropriate identity type).  If they don't synthesize, you can give their endpoints explicitly by enclosing them in curly braces:

.. code-block:: none

   ap f {a₀} {a₁} a₂ : Id B (f a₀) (f a₁)
   ap g {a₀} {a₁} a₂ {b₀} {b₁} b₂ : Id C (g a₀ b₀) (g a₁ b₁)

However, if you do this, then the function ``f`` must synthesize in order for the whole expression to synthesize.  If the whole expression is in a checking context, then it suffices for the function to be an abstraction with explicit domain such as ``(x : A) ↦ …``.

At the moment it is not obvious how to generalize ``ap`` to dependent functions; we will return to this later.

Finally, the operations ``refl`` and ``ap`` also satisfy various intuitive laws.  For instance, we have definitional equalities:

.. code-block:: none

   ap (x ↦ x) a₂ ≡ a₂
   ap (_ ↦ b) a₂ ≡ refl b
   ap (g ∘ f) a₂ ≡ ap g (ap f a₂)
   ap f (refl a) ≡ refl (f a)


Id of record types
------------------

The property of identity types that makes them *observational* is that they *compute* based on the type, to another type of the same kind.  That is, the identity types of a record type compute to another record type, the identity types of a data type compute to another data type, etc.  Similarly, ``refl`` and ``ap`` also compute on introduction and elimination forms.

For example, consider a binary product:

.. code-block:: none

   def Prod (A B : Type) : Type ≔ sig (
     fst : A,
     snd : B )

In this case, the identity type ``Id (Prod A B) u v`` reduces to a record type that is written

.. code-block:: none

   Prod⁽ᵉ⁾ (Id A) (Id B) u v

The superscript ``⁽ᵉ⁾`` indicates that this is a higher-dimensional version of ``Prod``.  This type is a record type with two fields of the following types:

.. code-block:: none

   fst : Id A (u .fst) (v .fst)
   snd : Id B (u .snd) (v .snd)

That is, if we have ``p : Prod⁽ᵉ⁾ (Id A) (Id B) u v``, then

.. code-block:: none

   p .fst : Id A (u .fst) (v .fst)
   p .snd : Id B (u .snd) (v .snd)

Dually, if we have

.. code-block:: none

   r : Id A (u .fst) (v .fst)
   s : Id B (u .snd) (v .snd)

then ``(r,s) : Prod⁽ᵉ⁾ (Id A) (Id B) u v``.

In general, the rule is that the identity types of a record type are again record types, with the same number of fields *with the same names*, whose types are the identity types of those of the original record type.  We will return later to what this means when the types of some fields are dependent on others.

Since ``Prod⁽ᵉ⁾ (Id A) (Id B) u v`` satisfies η-conversion, it is "definitionally isomorphic" to ``Prod (Id A (u .fst) (v .fst)) (Id B (u .snd) (v .snd))``, i.e. there are functions in both directions whose composites in both orders are definitionally equal to identities.  This further justifies the notation ``Prod⁽ᵉ⁾``: this is *a* product type, though not definitionally equal to an ordinary product type.  (However, for a general record type it may not be possible to say something quite like this.)

The notation suggests that ``Id A`` and ``Id B`` as well as ``u`` and ``v`` are *parameters* of the record type ``Prod⁽ᵉ⁾``.  This is in fact true, but we postpone discussing it until later after we talk about what type ``Id A`` and ``Id B`` have.

The other operations ``refl`` and ``ap`` also compute when applied to terms associated to records (projections and tuples).  For instance:

1. ``refl (a, b)`` reduces to ``(refl a, refl b)``.
2. ``refl (u .fst)`` reduces to ``refl u .fst`` (which, recall, means ``(refl u) .fst``), and similarly for ``snd``.
3. ``ap (x ↦ (f x, g x)) u₂`` reduces to ``(ap f u₂, ap g u₂)`` (modulo η-converting ``(x ↦ f x) : A → B`` to ``f`` and similarly).
4. ``ap ((x ↦ f x .fst) : A → B) u₂`` reduces to ``ap f u₂ .fst``, and similarly for ``snd``.
5. Multi-variable functions work similarly: ``ap (x y ↦ g x y .fst) u₂ v₂`` reduces to ``ap g u₂ v₂ .fst`` and so on.


Id of codatatypes
-----------------

Similarly, identity types of codatatypes compute to types of bisimulations.  For instance, if we have ``Stream`` defined as usual:

.. code-block:: none

   def Stream (A : Type) : Type ≔ codata [
   | _ .head : A
   | _ .tail : Stream A ]

Then ``Id (Stream A) s t`` reduces to ``Stream⁽ᵉ⁾ (Id A) s t``, which is a codatatype with fields

.. code-block:: none

   | _ .head : Id A (s .head) (t .head)
   | _ .tail : Id (Stream A) (s. tail) (t .tail)

In other words, an element of ``Stream⁽ᵉ⁾ (Id A) s t`` is a *stream of equalities*, again justifying the notation ``Stream⁽ᵉ⁾``.  Individual bisimulations, i.e. elements of ``Stream⁽ᵉ⁾ (Id A) s t``, can then be constructed by comatching and corecursion.

Just as for record types, ``refl`` and ``ap`` compute straightforwardly on field projections for codatatypes.  However, since a comatch is always part of a case tree, which never computes until a field projection is applied, the same is true for ``refl`` and ``ap`` of it.  For instance, if we define a stream of natural numbers:

.. code-block:: none

   def nats (n : ℕ) : Stream ℕ ≔ [
   | .head ↦ n
   | .tail ↦ nats (suc. n) ]

then ``refl (nats 0)`` does not reduce to anything.  However, if we apply some destructors to it, such as ``refl (nats 0) .tail .tail .head``, then it does compute in the expected way (in this case, to ``refl 2``).


Id of datatypes
---------------

As with records and codatatypes, the identity types of a datatype are again datatypes, whose constructors have types involving the identity types of those of the original.  In this case, the *endpoints* of the identity type behave like *indices* of its definition rather than parameters.  For instance, consider the usual sum type:

.. code-block:: none

   def Sum (A B : Type) : Type ≔ data [
   | left. (a : A) : Sum A B
   | right. (b : B) : Sum A B ]

Then ``Id (Sum A B) u v`` reduces to ``Sum⁽ᵉ⁾ (Id A) (Id B) u v``, which is a datatype with constructors

.. code-block:: none

   | left. {a₀ a₁ : A} (a₂ : Id A a₀ a₁) : Sum⁽ᵉ⁾ (Id A) (Id B) (left. a₀) (left. a₁)
   | right. {b₀ b₁ : B} (b₂ : Id B b₀ b₁) : Sum⁽ᵉ⁾ (Id A) (Id B) (right. b₀) (right. b₁)

Thus, as before, ``Sum⁽ᵉ⁾ (Id A) (Id B) u v`` is again *a* sum type.  The endpoints are indices because their occurrences ``(left. a₀) (left. a₁)`` and ``(right. b₀) (right. b₁)`` in the outputs of the constructors are not fully general, but are determined by the inputs.  (The arguments ``Id A`` and ``Id B`` are also not fully general, but they are the same as those given to ``Sum⁽ᵉ⁾``, and when we give the general type of ``Sum⁽ᵉ⁾`` below it will be clear that these arguments are actually parameters.)

We have written the input endpoints such as ``a₀ a₁`` with curly braces to indicate that they are implicit, as with the endpoint arguments of ``ap f``.  However, in this case it is *not* possible to give these arguments explicitly when applying the constructors ``left.`` and ``right.``.  But there is unlikely to be any need to, since constructors *and* their arguments always check rather than needing to synthesize.

It is possible, however, to omit some of the arguments of a higher constructor and check it at a higher function-type.  For instance, for any fixed types ``A`` and ``B``, the constructor ``left.`` checks at type ``{a₀ a₁ : A} (a₂ : Id A a₀ a₁) →⁽ᵉ⁾ Sum⁽ᵉ⁾ (Id A) (Id B) (left. a₀) (left. a₁)`` (see :ref:`Id of function types`, below).

Recursive cases are similar, e.g. for lists

.. code-block:: none

   def List (A : Type) : Type ≔ data [
   | nil. : List A
   | cons. (x : A) (xs : List A) : List A ]

the identity type ``Id (List A) p q`` reduces to ``List⁽ᵉ⁾ (Id A) p q``, which is again a type of *lists of equalities*, with constructors

.. code-block:: none

   | nil. : List⁽ᵉ⁾ (Id A) nil. nil.
   | cons. {x₀ x₁ : A} (x₂ : Id A x₀ x₁) {xs₀ xs₁ : List A} (xs₂ : List⁽ᵉ⁾ (Id A) xs₀ xs₁)
       : List⁽ᵉ⁾ (Id A) (cons. x₀ xs₀) (cons. x₁ xs₁)

As with record types, the other primitives ``refl`` and ``ap`` compute on terms associated to datatypes (constructors and matches).  In the case of constructors, we have for example

1. ``refl (left. a)`` reduces to ``left. (refl a)``, and similarly for ``right``.
2. ``refl (cons. x (cons. y nil.))`` reduces to ``cons. (refl x) (cons. (refl y) nil.)``.
3. ``refl 3``, which means ``refl (suc. (suc. (suc. zero.)))``, reduces to ``suc. (suc. (suc. zero.))`` where all the constructors denote higher-dimensional ones.  Since a numeral checks at *any* datatype having the appropriate constructors, ``refl 3`` can also be written as just ``3``.  However, since this may look confusing, Narya prints it as ``refl 3`` even though the ``refl`` is strictly speaking unnecessary.

Since matches (like comatches) are case tree constructs, ``refl`` and ``ap`` of functions defined using matching don't compute until they are applied to constructors.  Thus, for instance, if we define addition of natural numbers:

.. code-block:: none

   def plus (m n : ℕ) : ℕ ≔ match m [
   | zero. ↦ n
   | suc. m ↦ suc. (plus m n) ]

then ``refl plus`` doesn't compute to anything, until we apply it to something involving a constructor.  For instance,

1. ``refl plus (suc. m₂) n₂``, where ``m₂ : Id ℕ⁽ᵉ⁾ m₀ m₁`` and ``n₂ : Id ℕ⁽ᵉ⁾ n₀ n₁``, computes to ``suc. (refl plus m₂ n₂)``.
2. Similarly but more simply, ``refl plus zero. n₂`` computes to ``n₂``.

It is also, of course, possible to match directly on a higher-dimensional datatype such as ``List⁽ᵉ⁾ (Id A)``.  However, this requires a new notation which we discuss below in :ref:`Cubes of variables`.


Id of function types
--------------------

Unsurprisingly, the identity types of function types are again function types; but in this case there are several subtleties.  Specifically, the identity type ``Id (A → B) f g`` reduces to a function type that is written

.. code-block:: none

  {x₀ x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B (f x₀) (g x₁)

As before, the superscript ``⁽ᵉ⁾`` indicates that this is a higher-dimensional type; but in terms of behavior it can be ignored.  Thus, an element ``h``  of this type is a function that can be applied to two arguments ``x₀`` and ``x₁`` of type ``A`` and a third argument ``x₂`` of type ``Id A x₀ x₁`` to produce an element of ``Id B (f x₀) (g x₁)``.

The curly braces around ``x₀`` and ``x₁`` indicate that they are "implicit arguments", not written by default in applications, so in the above situation we write ``h x₂ : Id B (f x₀) (g x₁)``.  Narya does not yet have general implicit arguments, but in this specific case it does, because they can be inferred in a consistent way: if ``x₂`` synthesizes (as it often does), then ``x₀`` and ``x₁`` are determined by its type.  However, if needed or desired (such as if ``x₂`` does not synthesize), the first two arguments can be supplied explicitly by putting curly braces around them, as in ``h {x₀} {x₁} x₂``.  Such an ``h`` cannot be "partially applied" to only one or two of the implicit arguments, however: all three arguments must be given at once.

Dually, an element of ``Id (A → B) f g`` can be defined as an abstraction of a term ``M : Id B (f x₀) (g x₁)`` over variables ``x₀ x₁ : A`` and ``x₂ : Id A x₀ x₁``.  In this case the implicit arguments *must* be named and enclosed in curly braces in the abstraction, as in ``{x₀} {x₁} x₂ ↦ M``.  (An alternative to this is to use :ref:`Cubes of variables`, discussed later.)

Of course, ``refl`` and ``ap`` also compute on terms associated to function types (application and abstraction).  In the case of application this is straightforward, for instance:

1. ``refl (f a)`` reduces to ``refl f (refl a)``, that is ``refl f {a} {a} (refl a)``.
2. ``ap (x ↦ (f x) (a x)) u₂`` reduces to ``ap f (ap a u₂)``.  If ``u₂ : Id X u₀ u₁``, then this is more specifically ``ap f {a u₀} {a u₁} (ap a u₂)``.

For abstraction, ``refl`` computes to ``ap``, while ``ap`` computes to an ``ap`` with one more variable.  Although, in fact these computations don't reduce fully until applied to arguments, as if they were defined by a case tree.  For instance:

1. ``refl (x ↦ M) a₂`` reduces to ``ap (x ↦ M) a₂``.
2. ``ap (x ↦ (y ↦ M)) a₂ b₂`` reduces to ``ap (x y ↦ M) a₂ b₂``.

These equations suggest that ``refl`` can be view as a "0-ary" version of ``ap``, which is correct.  In fact, more is true: by η-expansion, for any function ``f : A → B`` we have

.. code-block:: none

   refl f
     ≡ ({x₀} {x₁} x₂ ↦ refl f x₂)
     ≡ ({x₀} {x₁} x₂ ↦ refl (x ↦ f x) x₂)
     ≡ ({x₀} {x₁} x₂ ↦ ap (x ↦ f x) x₂)
     ≡ ({x₀} {x₁} x₂ ↦ ap f x₂)

Thus, ``ap`` is in fact just a notational variant of ``refl``, which is preferred by convention (and used by Narya when printing terms) when its argument is a function.  In particular, we can write ``ap f`` without applying it to an argument, and it means the same as ``refl f``.  Note also that the law ``ap f (refl a) ≡ refl (f a)`` mentioned above can now be seen as actually the *reverse* of the computation law ``refl (f a) ≡ refl f (refl a)`` for reflexivity of application.


Cubes of variables
------------------

As previously noted, even though boundary arguments of higher-dimensional function *applications* are implicit, those arguments must always be given explicitly in higher-dimensional *abstractions*, though marked as "implicit" with braces as in ``{x₀} {x₁} x₂ ↦ M``.  However, there is a different shorthand syntax for higher-dimensional abstractions: instead of ``{x₀} {x₁} x₂ ↦ M`` you can write ``x ⤇ M`` (or ``x |=> M`` in ASCII).  This binds ``x`` as a "family" or "cube" of variables whose names are suffixed with face names; in this case they are ``x.0`` and ``x.1`` and ``x.2`` (see :ref:`Higher-dimensional cubes` for the general case).  The unsuffixed name ``x`` can also be used as a shorthand for the top-dimensional face ``x.2``.

Note that this is a *purely syntactic* abbreviation: there are really *three different variables* that happen to have the names ``x.0`` and ``x.1`` and ``x.2``, with ``x`` considered an alias for ``x.2``.  There is no potential for collision with user-defined names, since ordinary local variable names cannot contain internal periods, and atomic identifiers cannot consist entirely of digits.  However, a cube variable with "base" name ``x`` does shadow, and is shadowed by, ordinary variables named ``x``, as well as other cube variables with base name ``x`` of different dimension.

Cubes of variables also appear automatically when matching against a higher-dimensional version of a datatype; and to indicate this, such matches use ``⤇`` rather than ``↦``.  For instance, we can do an encode-decode proof for the natural numbers by matching directly on ``Id ℕ`` (using pattern-matching abstractions):

.. code-block:: none

   def code : ℕ → ℕ → Type ≔ [
   | zero. ↦ [
     | zero. ↦ sig ()
     | suc. n ↦ data []]
   | suc. m ↦ [
     | zero. ↦ data []
     | suc. n ↦ sig ( uncode : code m n ) ]]
   
   def decode : (m n : ℕ) → code m n → Id ℕ m n ≔ [
   | zero. ↦ [
     | zero. ↦ _ ↦ zero.
     | suc. n ↦ [] ]
   | suc. m ↦ [
     | zero. ↦ []
     | suc. n ↦ p ↦ suc. (decode m n (p .0)) ]]
   
   def encode (m n : ℕ) : Id ℕ m n → code m n ≔ [
   | zero. ⤇ ()
   | suc. p ⤇ (_ ≔ encode p.0 p.1 p.2)]

Here in the definition of ``encode``, the pattern variable ``p`` of the ``suc.`` branch is automatically made into a 1-dimensional cube of variables since we are matching against an element of ``Id ℕ``, so in the body we can refer to ``p.0``, ``p.1``, and ``p.2``.  And because of this, we are required to use ``⤇`` rather than ``↦`` to introduce the bodies of branches in that ``match``.

Unlike for abstractions, for higher-dimensional matches there is no option to write ``↦`` and name all the variables explicitly (e.g. ``| suc. {p0} {p1} p2 ↦``).  We deem this would be too confusing, because higher-dimensional constructors can never be *applied* explicitly to all their boundaries, and a "pattern" in a ``match`` should look as much as possible like the constructor that it matches against.

It is possible to do :ref:`Multiple matches and deep matches` that combine zero- and higher-dimensional matches.  In this case the match symbol is ``⤇``, which we can think of as indicating that at least *some* of the pattern variables are nontrivial cubes.  (In fact, currently the symbol ``⤇`` is allowed for *all* multiple and deep matches, even if none of them are higher-dimensional, but this should not be depended on.)


Id of the universe
------------------

Since the universe ``Type`` is a type, for any elements ``A B : Type`` we have an identity type ``Id Type A B``.  The actual definition of this type depends on whether we are in :ref:`Parametricity` or :ref:`Higher Observational Type Theory`, but here we discuss the aspects of its behavior that are common to both.  Namely, every ``R : Id Type A B`` induces a *correspondence* between ``A`` and ``B``: a family of types ``R a b`` depending on ``a : A`` and ``b : B``.  (We avoid the word "relation" since it erroneously suggests proposition-valued.)  The notation ``R a b`` looks like function application, but it is not exactly since ``R`` is not a function; instead we call it *instantiation* of ``R`` at ``a`` and ``b``.  It can be thought of as implicitly coercing ``R`` to an "underlying function" and then applying that to ``a`` and ``b``.

Of course, every ``A : Type`` also has a reflexivity term ``refl A : Id Type A A``.  The underlying correspondence of ``refl A``. is defined to be the identity types of ``A``.  That is:

- The instantiation ``refl A x y`` reduces to the identity type ``Id A x y``.

In fact, ``Id`` is just another notational variant of ``refl``, which is preferred by convention (and used by Narya when printing terms) when its argument is a type.  In particular, we can write ``Id A`` without instantiating it, and it means the same as ``refl A``.  Thus we have ``Id A : Id Type A A``.

Understanding ``Id Type`` also makes sense of the notation ``Prod⁽ᵉ⁾ (Id A) (Id B) u v`` from :ref:`Id of record types`.  Specifically, since ``Prod : Type → Type → Type``, we have

.. code-block:: none

   refl Prod : {A₀ A₁ : Type} (A₂ : Id Type A₀ A₁) {B₀ B₁ : Type} (B₂ : Id Type B₀ B₁)
                 →⁽ᵉ⁾ Id Type (Prod A₀ B₀) (Prod A₁ B₁)

This suggests that ``⁽ᵉ⁾`` is just *another* notational variant of ``refl``.  For then ``Prod⁽ᵉ⁾`` (that is, ``refl Prod``) has exactly the correct type to be applied to two (explicit) arguments ``Id A : Id Type A A`` and ``Id B : Id Type B B`` to obtain an element of ``Id Type (Prod A B) (Prod A B)``, which can then be instantiated at ``u`` and ``v`` to produce a type.

In particular, this makes sense of un-applied ``Prod⁽ᵉ⁾``, and un-instantiated higher-dimensional types such as ``Prod⁽ᵉ⁾ (Id A) (Id B)`` (the reduct of un-instantiated ``Id (Prod A B)``).  We can also consider un-instantiated ``Id (A → B)``, but in this case we need a new notation for what it reduces to, since the previously introduced notation ``{x₀ x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B (f x₀) (g x₁)`` doesn't make sense without an ``f`` and a ``g``.  The new notation we use for this is ``Id A ⇒ Id B``.  In particular, therefore, the fully instantiated version ``Id (A → B) f g`` can also be written as ``(Id A ⇒ Id B) f g``.


Heterogeneous identity types
----------------------------

Now suppose ``B : A → Type`` and ``x₂ : Id A x₀ x₁``.  Then ``ap B x₂ : Id Type (B x₀) (B x₁)``, so it has instantiations.  That is, given ``y₀ : B x₀`` and ``y₁ : B x₁``, we have a type ``ap B x₂ y₀ y₁``, whose elements we call of *heterogeneous* identifications/bridges relating ``y₀`` and ``y₁`` "along" or "over" ``x₂``.  Since ``Id`` is a notational variant of ``ap`` (i.e. ``refl``), this type can also be written suggestively as ``Id B x₂ y₀ y₁`` (and Narya does this when printing: for the special case of ``Type``-valued functions we prefer ``Id`` over ``refl`` or ``ap``.)

Note that since ``ap`` of a constant function reduces to ``refl``, heterogeneous ``Id`` of a constant type family reduces to ordinary ``Id``.  That is:

.. code-block:: none

  Id (_ ↦ B) x₂ y₀ y₁ ≡ Id B y₀ y₁

Such heterogeneous identity types are used in the computation of identity types of *dependent* records, function types, and so on.  For instance, if we define

.. code-block:: none

   def Σ (A : Type) (B : A → Type) : Type ≔ sig (
     fst : A,
     snd : B fst )

then ``Id (Σ A B) u v`` reduces to ``Σ⁽ᵉ⁾ (Id A) (Id B) u v``, which is a record type with fields

.. code-block:: none

   fst : Id A (u .fst) (v .fst)
   snd : Id B fst (u .snd) (v .snd)

Similarly, ``Id ((x:A) → B x) f g`` reduces to a higher-dimensional function type

.. code-block:: none

   {x₀ x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B x₂ (f x₀) (g x₁)

whose behavior generalizes that described for non-dependent function types in :ref:`Id of function types`.  Since heterogeneous ``Id`` of a constant family reduces to ordinary ``Id``, this is consistent with the definition above of ``Id`` for non-dependent function types.

The un-instantiated version ``Id ((x:A) → B x)`` likewise reduces to a dependently typed version of the previously introduced notation, ``(x : Id A) ⇒ Id B x.2``.  Here ``x`` is a cube of variables, and the symbol ``⇒`` is of course intentionally reminiscent of ``⤇``.

In particular, since ``Σ : (A : Type) (B : A → Type) → Type``, the type of ``Id Σ`` is

.. code-block:: none

   {A₀ : Type} {A₁ : Type} (A₂ : Id Type A₀ A₁)
   {B₀ : A₀ → Type} {B₁ : A₁ → Type}
   (B₂ : {x₀ : A₀} {x₁ : A₁} (x₂ : A₂ x₀ x₁) →⁽ᵉ⁾ Id Type (B₀ x₀) (B₁ x₁))
     →⁽ᵉ⁾ Id Type (Σ A₀ B₀) (Σ A₁ B₁)

Thus, ``Σ⁽ᵉ⁾`` has has exactly the correct type to be applied to ``Id A : Id Type A A`` and ``Id B : {x₀ x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id Type (B x₀) (B x₁))`` to produce an element of ``Id Type (Σ A B) (Σ A B)``, which can then be instantiated at ``u`` and ``v`` to yield a type, explaining the above notation ``Σ⁽ᵉ⁾ (Id A) (Id B) u v``.  Other canonical types behave similarly.


Higher-dimensional cubes
------------------------

Iterating ``Id`` or ``refl`` multiple times produces higher-dimensional types, whose elements are higher-dimensional cubes.  Specifically, an *n*-dimensional type can be instantiated at variables representing the boundary of an *n*-dimensional cube, yielding an ordinary (0-dimensional) type whose elements are fillers for that boundary.  However, this does not need to be stipulated by hand, but emerges automatically from what we have already introduced.

The main new ingredient is that since an element ``R : Id Type A B`` can be instantiated at elements of ``A`` and ``B`` to yield a type, it makes sense to think of it as having an underlying function of type ``A → B → Type``, which it is coerced to by instantiation.  Therefore, its reflexivity/identity term ``Id R`` should have an underlying function of type

.. code-block:: none

   {a₀ a₁ : A} (a₂ : Id A a₀ a₁) {b₀ b₁ : B} (b₂ : Id B b₀ b₁) →⁽ᵉ⁾ Id Type (R a₀ b₀) (R a₁ b₁)

The output of this function can then be further instantiated at elements ``r₀ : R a₀ b₀`` and ``r₁ : R a₁ b₁``.  Therefore, for any arguments of appropriate types, we have a type

.. code-block:: none

   Id R {a₀} {a₁} a₂ {b₀} {b₁} b₂ r₀ r₁ : Type

As a special case, if ``R`` is ``Id A : Id Type A A``, then such an instantiation becomes

.. code-block:: none

   Id (Id A) {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁

(or just ``Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁``), where the types of the arguments are

.. code-block:: none

   {a₀₀ : A}
   {a₀₁ : A}
   (a₀₂ : Id A a₀₀ a₀₁)
   {a₁₀ : A}
   {a₁₁ : A}
   (a₁₂ : Id A a₁₀ a₁₁)
   (a₂₀ : Id A a₀₀ a₁₀)
   (a₂₁ : Id A a₀₁ a₁₁)

We view these as forming the boundary of a 2-dimensional square, with ``Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁`` the type of fillers inhabiting that boundary.  Similarly, ``Id (Id (Id A))`` can be instantiated to yield types of 3-dimensional cubes, and so on.

Of course, the variables in the boundary of a square can be named anything you want.  However, the naming scheme with subscripts used above is systematic and has certain advantages.  Specifically, a cube of dimension *n* has 3ⁿ faces, including the center one (which is missing in a boundary), and we name them by the numbers from 0 to 3ⁿ−1 written in base-3 notation.  The intrinsic dimension of a face is then the number of 2s in its base-3 representation, and *its* codimension-1 faces are obtained by replacing one of the 2s with a 0 or a 1.  The overall codimension-1 faces, which are the only explicit ones in an instantiation, are those in which all the digits are 2s except one.  Finally, the variables in an instantiation or higher-dimensional function application appear in increasing ternary order.  In particular, Narya uses this naming scheme for :ref:`Cubes of variables` of all dimensions, although with dot-suffixes rather than subscripts; we will return to this below.

In any case, the squares described by ``Id (Id A)`` are "totally homogeneous", with everything living in the same type ``A``; whereas the previously mentioned case of ``Id R : Id (Id Type A B) R R`` is homogeneous in one dimension (with some boundary components like ``a₂ : Id A a₀ a₁`` living entirely in one type ``A``) and heterogeneous in the other (with other boundary components like ``r₀ : R a₀ b₀`` connecting one type ``A`` to another type ``B``).  But we can also consider types of totally *heterogeneous* squares.  To explain this, observe that by the homogeneous case, we can instantiate ``Id (Id Type)`` at a family of arguments of the following types:

.. code-block:: none

   {A₀₀ : Type}
   {A₀₁ : Type}
   (A₀₂ : Id Type A₀₀ A₀₁)
   {A₁₀ : Type}
   {A₁₁ : Type}
   (A₁₂ : Id Type A₁₀ A₁₁)
   (A₂₀ : Id Type A₀₀ A₁₀)
   (A₂₁ : Id Type A₀₁ A₁₁)

An inhabitant of the resulting type, ``A₂₂ : Id Type A₀₂ A₁₂ A₂₀ A₂₁``, then has an underlying "two-dimensional correspondence" that can be accessed by instantiating it at arguments of the following types:

.. code-block:: none

   {a₀₀ : A₀₀}
   {a₀₁ : A₀₁}
   (a₀₂ : A₀₂ a₀₀ a₀₁)
   {a₁₀ : A₁₀}
   {a₁₁ : A₁₁}
   (a₁₂ : A₁₂ a₁₀ a₁₁)
   (a₂₀ : A₂₀ a₀₀ a₁₀)
   (a₂₁ : A₂₁ a₀₁ a₁₁)

The result is a type ``A₂₂ a₀₂ a₁₂ a₂₀ a₂₁`` whose elements are totally heterogeneous squares with this specified boundary.

Note that unlike a 1-dimensional type, a higher-dimensional type *can* be "partially instantiated", but not arbitrarily: you must give exactly enough arguments to reduce it to a type of some specific lower dimension.  For a 2-dimensional type such as ``A₂₂`` above, this means that in addition to its full 0-dimensional instantiations such as ``A₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁``, it has partial 1-dimensional instantiations such as

.. code-block:: none

   A₂₂ {a₀₀} {a₀₁} a₀₂ {a₁₀} {a₁₁} a₁₂ : Id Type (A₂₀ a₀₀ a₁₀) (A₂₁ a₀₁ a₁₁)

This has exactly the right type that it can be *further* instantiated by ``a₂₀ a₂₁`` to produce a 0-dimensional type.  Similarly, a 3-dimensional type can be instantiated first at 18 arguments (of which two are explicit) to yield a 2-dimensional type, then at 6 more arguments to yield a 1-dimensional type, then at 2 last ones to yield a 0-dimensional (ordinary) type.

In general, a full instantiation of a higher-dimensional type takes only the *highest-dimensional* arguments explicitly; the others are inferred from their boundaries (which are required to match up correctly where they overlap).  In this case there are some half measures: if you give any lower-dimensional argument explicitly you must give all the arguments in that "block" explictly, but you can omit those in other blocks; for instance you can write ``Id (Id A) {a₀₀} {a₀₁} a₀₂ a₁₂ a₂₀ a₂₁`` or ``Id (Id A) a₀₂ {a₁₀} {a₁₁} a₁₂ a₂₀ a₂₁``.

Higher identity types compute on canonical types in a similar way to the 1-dimensional ones discussed above.  For instance, ``Id (Id (Prod A B)) u₀₂ u₁₂ u₂₀ u₂₁`` reduces to

.. code-block:: none

   Prod⁽ᵉᵉ⁾ (Id (Id A)) (Id (Id B)) u₀₂ u₁₂ u₂₀ u₂₁

which is a product of the two types

.. code-block:: none

   Id (Id A) (u₀₂ .fst) (u₁₂ .fst) (u₂₀ .fst) (u₂₁ .fst)
   Id (Id B) (u₀₂ .snd) (u₁₂ .snd) (u₂₀ .snd) (u₂₁ .snd)

Notationally, since repeated ``Id`` gets cumbersome, in higher dimensions Narya prints all identity types with the superscript syntax; thus the above would actually be printed

.. code-block:: none

   Prod⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ u₀₂ u₁₂ u₂₀ u₂₁

Similarly, ``Id (Id ((x : A) → B x)) f₀₂ f₁₂ f₂₀ f₂₁`` reduces to a function-type

.. code-block:: none

   {a₀₀ a₀₁ : A} {a₀₂ : Id A a₀₀ a₀₁} {a₁₀ a₁₁ : A} {a₁₂ : Id A a₁₀ a₁₁}
   {a₂₀ : Id A a₀₀ a₁₀} {a₂₁ : Id A a₀₁ a₁₁} (a₂₂ : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁)
     →⁽ᵉᵉ⁾ Id (Id B) (f₀₂ a₀₂) (f₁₂ a₁₂) (f₂₀ a₂₀) (f₂₁ a₂₁)

Note that in this case, all the arguments are implicit except the last, highest-dimensional, one ``a₂₂``.  This remains true in higher dimensions.  As usual,  it is possible to give the implicit arguments explicitly by surrounding them with curly braces, as in ``refl f {a₀} {a₁} a₂``, but if you do this you must give *all* of them explicitly; there are no half measures.  As before, the main reason you might need to do this is if the top-dimensional argument is a term that doesn't synthesize; but it can also be helpful sometimes for clarity.

Of course, one inhabitant of such a higher-dimensional function type is ``refl (refl f)``, or equivalently ``ap (ap f)``, which Narya actually displays as ``f⁽ᵉᵉ⁾``.  Thus we have

.. code-block:: none

   f⁽ᵉᵉ⁾ : {a₀₀ a₀₁ : A} {a₀₂ : Id A a₀₀ a₀₁} {a₁₀ a₁₁ : A} {a₁₂ : Id A a₁₀ a₁₁}
           {a₂₀ : Id A a₀₀ a₁₀} {a₂₁ : Id A a₀₁ a₁₁} (a₂₂ : Id (Id A) a₀₂ a₁₂ a₂₀ a₂₁)
             →⁽ᵉᵉ⁾ Id (Id B) (ap f a₀₂) (ap f a₁₂) (ap f a₂₀) (ap f a₂₁)

We can define other higher-dimensional functions by abstraction.  Analogously to the 1-dimensional case, all the lower-dimensional implicit arguments must be named in an ordinary abstraction and surrounded by braces, such as

.. code-block:: none

   {x₀₀} {x₀₁} {x₀₂} {x₁₀} {x₁₁} {x₁₂} {x₂₀} {x₂₁} x₂₂ ↦ …

However, the alternative of :ref:`Cubes of variables` is also available and often more convenient.  For a 2-dimensional abstraction, for instance, you can write simply ``x ⤇ …`` to bind nine variables named from ``x.00`` through ``x.22`` (with ``x`` an alias for the top-dimensional face ``x.22``).  The dimension of the cube of variables is inferred from the type at which the abstraction is checked, and *may not* be zero: if the dimension is zero, you must use ``↦`` instead.  And as with ordinary abstractions, multiple cube abstractions can be combined as in ``x y ⤇ M``, but all the variables combined in this way must have the same dimension (which is nonzero); otherwise you must write ``x ⤇ y ⤇ M`` or ``x ↦ y ⤇ M``, etc.  (These restrictions are an intentional choice intended to increase readability; but if you don't like them, please give feedback.)


Implicit boundaries
-------------------

We have noted above that many parts of the boundary of a cube are treated as implicit arguments.  Normally, Narya also hides these arguments when printing such terms and types.  However, you can tell it to print these arguments explicitly with the commands

.. code-block:: none

   display function boundaries ≔ on
   display type boundaries ≔ on

(and switch back with ``≔ off``).  These commands are not available in source files, since they should not be part of the "time stream" of undoables.  They can be given in interactive mode, or with the ProofGeneral commands ``C-c C-d C-f`` and ``C-c C-d C-t``, or you can use the corresponding command-line flags such as ``-show-function-boundaries``.  When these options are ``on``, Narya prints *all* the lower-dimensional arguments explicitly, with curly braces around them.  There are (currently) no half measures here, for functions or for types.

In addition, even when printing implicit boundaries is off, Narya attempts to be smart and print those boundaries when it thinks that they would be necessary in order to re-parse the printed term because the corresponding explicit argument isn't synthesizing.  In this case it can do half measures, the way you can when writing type boundaries: the implicit arguments in each "block" are printed only if the primary argument of that block is nonsynthesizing.


Symmetries and degeneracies
---------------------------

There is a symmetry operation ``sym`` that acts on at-least-two dimensional cubes, swapping or transposing the last two dimensions.  Like ``refl``, if the argument of ``sym`` synthesizes, then the ``sym`` synthesizes a symmetrized type; but in this case the argument must synthesize a "2-dimensional" type.  And also as with ``refl``, an application of ``sym`` can also check, in this case by symmetrizing the checking type to check its argument.

Combining versions of ``refl`` and ``sym`` yields arbitrary higher-dimensional "degeneracies" (from the BCH cube category).  There is also a generic syntax for such degeneracies, for example ``M⁽²ᵉ¹⁾`` or ``M^^(2e1)`` where the superscript represents the degeneracy, with ``e`` denoting a degenerate dimension and nonzero digits denoting a permutation.  (The ``e`` stands for "equality", as we are using the notation of :ref:`Higher Observational Type Theory`; when using :ref:`Parametricity` instead you can change the letter.)  In the unlikely event you are working with dimensions greater than nine, you can separate multi-digit numbers and letters with a hyphen, e.g. ``M⁽¹⁻²⁻³⁻⁴⁻⁵⁻⁶⁻⁷⁻⁸⁻⁹⁻¹⁰⁾`` or ``M^^(0-1-2-3-4-5-6-7-8-9-10)``.

As with ``refl`` and ``sym``, this notation synthesizes if ``M`` does, and can always check.  If the degeneracy is not a pure symmetry (that is, it contains one or more ``e`` s), you can write ``_`` for the term in a checking context, since it is determined by the output type, e.g. ``_⁽ᵉᵉ⁾ : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)`` will infer ``a`` for the placehold.  Finally, if ``M`` is a 0-dimensional abstraction and the degeneracy is immediately applied to arguments such as ``(x y ↦ P)⁽ᵉᵉ⁾ a₂₂ b₂₂``, it is treated as a "higher-dimensional redex" and subject to the rules laid out for :ref:`Checking redexes`: each argument must either synthesize or have the corresponding domain given explicitly in the abstraction, and either the body of the abstraction must synthesize or the whole application must be in a checking context.

Degeneracies can be extended by identities on the left and remain the same operation.  For instance, the two degeneracies taking a 1-dimensional object to a 2-dimensional one are denoted ``1e`` and ``e1``, and of these ``1e`` can be written as simply ``e`` and coincides with ordinary ``refl`` applied to an object that happens to be 1-dimensional.  Similarly, the basic symmetry ``sym`` of a 3-dimensional object actually acts on the last two dimensions, so it coincides with the superscripted operation ``132``.

A mnemonic for the names of permutation operators is that the permutation numbers indicate the motion of arguments.  For instance, if we have a 3-dimensional cube

.. code-block:: none

   a222 : Id (Id (Id A))
     {a000} {a001} {a002} {a010} {a011} {a012} {a020} {a021} a022
     {a100} {a101} {a102} {a110} {a111} {a112} {a120} {a121} a122
     {a200} {a201} a202 {a210} {a211} a212 a220 a221

then to work out the boundary of a permuted cube such as ``a222⁽³¹²⁾``, consider the motion of the "axes" ``a001``, ``a010``, and ``a100``.  The permutation notation ``(312)`` denotes the permutation sending 1 to 3, sending 2 to 1, and sending 3 to 2.  Therefore, the first axis ``a001`` moves to the position previously occupied by the third axis ``a100``, the second axis ``a010`` moves to the position previously occupied by the first axis ``a001``, and the third axis ``a100`` moves to the position previously occupied by the second axis ``a010``.  This determines the motion of the other boundary faces (although not which of them end up symmetrized):

.. code-block:: none

   a222⁽³¹²⁾ : A⁽ᵉᵉᵉ⁾
     {a000} {a010} {a020} {a100} {a110} {a120} {a200} {a210} a220
     {a001} {a011} {a021} {a101} {a111} {a121} {a201} {a211} a221
     {a002} {a012} (sym a022) {a102} {a112} (sym a122) (sym a202) (sym a212)

Degeneracy operations are functorial.  For pure symmetries, this means composing permutations.  For instance, the "Yang-Baxter equation" holds, equating ``M⁽²¹³⁾⁽¹³²⁾⁽²¹³⁾`` with ``M⁽¹³²⁾⁽²¹³⁾⁽¹³²⁾``, as both reduce to ``M⁽³²¹⁾``.  Reflexivities also compose with permutations in a fairly straightforward way, e.g. ``M⁽¹ᵉ⁾⁽²¹⁾`` reduces to ``M^⁽ᵉ¹⁾``.

The principle that the identity types of a canonical type are again canonical types of the same sort applies also to symmetries and higher degeneracies of such types, with one exception that we will discuss in :ref:`Parametricity`.
