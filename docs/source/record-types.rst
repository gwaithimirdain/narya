Record types and tuples
=======================

We now describe the various other classes of types that can be defined by the user, starting with the simplest, record types.

Defining record types
---------------------

A record type is defined by a number of *fields*, each with a declared type.  A constant of type ``Type`` can be defined to be a record type in a ``def`` statement by using the keyword ``sig`` and listing the fields with their types in parentheses, separated by commas.  For instance, we could bundle a type with an operation on it:

.. code-block:: none
   
   def Magma : Type ≔ sig (
      t : Type,
      op : t → t → t,
      )

The trailing comma after the last field is optional.  (By the lexing rules for :ref:`tokens`, no space is required around the commas, unless they follow a type that is expressed using a notation that ends with another special ASCII character.)  Note that later fields can depend on the values of previous fields, by name.  The names of fields must be valid local variable names, i.e. identifiers not containing periods.

Although this command may look like it is defining ``Magma`` to equal a pre-existing type denoted ``sig (t:Type, op:t→t→t)``, in fact it declares ``Magma`` to be a *new* type that didn't previously exist and doesn't reduce to anything else.  In particular, therefore, declaring another identical-looking type:

.. code-block:: none

   def Magma' : Type ≔ sig (
      t : Type,
      op : t → t → t,
      )

will yield a different result: ``Magma`` and ``Magma'`` are not convertible (although they will be isomorphic).

Like any definition, record types can have parameters.  For example, Σ-types are just a record type that can be defined by the user, if you wish:

.. code-block:: none
   
   def Σ (A : Type) (B : A → Type) : Type ≔ sig (
      fst : A,
      snd : B fst,
      )

However, we consider it better style in general to use specialized record types rather than generic Σ-types, as it provides better error-checking and documentation of the meaning of the fields.  It is also probably more efficient to use one record type with a lot of fields than an iterated Σ-type.  In the future we plan to implement metaprogramming-like capabilities for proving theorems about arbitrary record types, so that using them in preference to generic Σ-types does not entail a loss of expressivity.

Currently user notations cannot bind variables, so it is not possible to define a binding notation such as ``(x : A) × B x`` for Σ-types.  But if we define a non-dependent product type, we can give it an infix notation:

.. code-block:: none

   def prod (A B : Type) : Type ≔ sig (
      fst : A,
      snd : B,
      )

   notation 2 prod : A "×" B ≔ prod A B

The fact that parameters can equivalently be abstracted over in the type and the term applies also to record type declarations.  That is, the above definition of Σ-types is entirely equivalent to

.. code-block:: none

   def Σ : (A:Type) → (A → Type) → Type ≔ A B ↦ sig (
      fst : A,
      snd : B fst,
      )

A record type can have only one field:

.. code-block:: none

   def wrapped_nat : Type ≔ sig ( unwrap : ℕ )

or even zero fields:

.. code-block:: none
   
   def ⊤ : Type ≔ sig ()

Tuples
------

To define an element of a record type we use a *tuple*, which consists of components separated by commas inside parentheses.  The most explicit kind of tuple labels each component by name, for instance:

.. code-block:: none
   
   def nat.magma : Magma ≔ (
      t ≔ ℕ,
      op ≔ plus,
      )

Again, the trailing comma is optional, the Unicode ≔ can be replaced by ASCII ``:=``, and neither of them normally requires surrounding space.  In this explicit version, the order of the fields doesn't matter: the above is equivalent to

.. code-block:: none
   
   def nat.magma : Magma ≔ (
      op ≔ plus,
      t ≔ ℕ,
      )

Note that whatever order they are written in a tuple, the fields will always be *typechecked* in the order specified in the *record type declaration*.  This is necessary because the types of later fields can depend on the values of earlier ones.

The names of the fields in a tuple can also be replaced by underscores or omitted entirely, and in this case the fields are taken from the type definition *in the order given there*.  If some fields are named and others are not, the unnamed fields are matched up with the fields in the type that aren't named explicitly in the tuple, again in order.  Thus, we can also write the above tuple as any of the following:

.. code-block:: none
   
   (ℕ, plus)
   (_ ≔ ℕ, _ ≔ plus)
   (ℕ, op ≔ plus)
   (t ≔ ℕ, plus)
   (op ≔ plus, ℕ)
   (plus, t ≔ ℕ)

but not, of course, ``(plus, ℕ)`` since that would try to interpret ``plus`` as the value of the field ``t``.  Unlabeled tuples are convenient for small examples, including familiar cases such as ``(0,0) : ℝ × ℝ``, but for records with large numbers of fields they are discouraged as being hard to understand and brittle.  (But some mathematicians do like to write, for instance, ``(G,m,e,i,a,l,r,v) : Group``, and that is allowed.)

As this discussion suggests, tuples *check*, and do not synthesize.  In particular, this means that, as for function abstractions, the same tuple can mean different things when checked at different types.  An unlabeled tuple ``(a,b)`` can check at *any* record type with two fields for which `a` checks at the type of the first field and ``b`` at the type of the second (possibly depending on the value of ``a``).  A labeled tuple such as ``(fst ≔ a, snd ≔ b)`` can likewise check at any such record type for which the names of the two fields are ``fst`` and ``snd``.  *Field names are not scoped or namespaced*: they belong to a flat global name domain, distinct from that of constants and variables.

Like record types, tuples can have zero fields:

.. code-block:: none
   
   def ⋆ : ⊤ ≔ ()

They can also have only one field, although the naïve notation ``(M)`` isn't allowed for this case since it would clash with ordinary parenthesized terms.  To write a 1-tuple you can label the field, perhaps with an underscore, or you can add a trailing comma:

.. code-block:: none

   def wrapped_zero : wrapped_nat ≔ (unwrap ≔ zero.)
   def wrapped_zero : wrapped_nat ≔ (_ ≔ zero.)
   def wrapped_zero : wrapped_nat ≔ (zero. ,)

Syntactically, tuples are an outfix notation that includes the parentheses, rather than an infix meaning of the comma; thus the parentheses are always required.  Tuples are not associative: neither ``(a, (b, c))`` nor ``((a, b), c)`` can be written as ``(a,b,c)``.  The latter belongs to a record type with three fields, whereas the former two belong to a record type with two fields, one of which is itself a record type with two fields.  (This aligns with the behavior of functional programming languages such as Haskell and OCaml.)


Accessing fields
----------------

If ``M`` belongs to a record type that has a field named ``fld``, then ``M .fld`` extracts the value of this field.  In particular, if ``M`` is a tuple, then this reduces to the corresponding component.  Note the space in ``M .fld``, which distinguishes it from a single identifier named ``M.fld`` in the namespace ``M``.

A field projection ``M .fld`` requires ``M`` to synthesize a record type, and then synthesizes the value of the field ``fld`` in that record type (with any earlier fields that it depends on replaced by the corresponding fields of ``M``).  Thus, if you want to write a "record redex" that creates a tuple and then immediately projects out one of its fields, you need to ascribe the tuple: ``((a, b) : Σ A B) .fst``.

Like unlabeled tuples that default to the order in which fields were declared in the record type, fields can also be projected out by index: ``M .0`` means the zeroth field declared in the record type, ``M .1`` means the first field, and so on.  It's important to note that this is in reference to the order in which fields were declared in the record *type*, not in any tuple, even if labels were used in the tuple to give the components in a different order.  For instance, ``((snd ≔ b, fst ≔ a) : Σ A B) .0`` equals ``a``.  As with tuples, positional field access is convenient for small examples (especially when using positional tuples as well), but confusing and brittle when there are many fields.


Parsing field projections
-------------------------

Field projections behave like a symbol-free left-associative infix operator of tightness +ω, and can therefore be interspersed with ordinary applications to form an "elimination spine": ```f a .fld b`` means ``((f a) .fld) b``, in which we successively "eliminate" ``f`` by applying it to an argument (the elimination rule of a function type), project out a field (the elimination rule of a record type), and then apply it to another argument.  Indeed, it can sometimes be helpful to think of an element of a record type as a "function" and of ``M .fld`` as "applying" it to the field name as an "argument".

It must be emphasized that *field projections bind with the same tightness as function application*, similarly associating to the left.  This applies even if the argument preceeding the field ends with a special character so that a space is not required, e.g. ``f (g a).fld b`` means ``((f (g a)) .fld) b``.  If you mean to project the field from ``g a``, you must write ``f ((g a).fld) b``, or better ``f (g a .fld) b``.  This convention differs from field projections in many functional languages such as OCaml and Haskell (although it matches the behavior of Agda), but we believe it is the correct choice in a language where function application is denoted by juxtaposition.  For example, in a language like Java where function calls are parenthesized, one frequently finds an idiom like

.. code-block:: none

   object.methodOne(x, y, z)
     .methodTwo(a, b)
     .methodThree(c, d, e)
     .methodFour()

to call a sequence of methods on each other's outputs.  In Narya and Agda, you can write the same thing even more simply without the parentheses:

.. code-block:: none

   object .methodOne x y z
     .methodTwo a b
     .methodThree c d e
     .methodFour

But in a language with application by juxtaposition but where field projection binds tighter than function application, such as OCaml and Haskell, you have to write lots of silly parentheses:

.. code-block:: none

   (((object.methodOne x y z)
     .methodTwo a b)
     .methodThree c d e)
     .methodFour

Eta-conversion and reduction
----------------------------

Records satisfy η-conversion: two elements of a record type whose components are field-wise convertible are themselves convertible.  For instance, if ``M : Σ A B``, then ``M`` is convertible with ``(M .fst, M .snd)``, although neither reduces to the other.  In particular, if a record type has zero fields, then it has a unique element ``()`` up to convertibility; and if it has only one field, it is definitionally isomorphic to the type of that field.

In addition, tuples are allowed as nodes in a case tree.  Thus, a constant that is defined to directly equal a tuple, or an abstracted tuple, or a tuple inside a let-binding, does not *reduce* to that tuple directly: it only reduces when a field is projected.  (Now we see why case trees are *trees*, as with tuple nodes they can in fact ramify into multiple branches.)  For instance, if we have

.. code-block:: none

   def pair (a:A) (b:B a) : Σ A B ≔ (a,b)

then ``pair a b`` doesn't reduce to ``(a,b)``.  But ``pair a b .fst`` does reduce to ``a`` and ``pair a b .snd`` does reduce to ``b``, which in turn means (by η-conversion) that ``pair a b`` is *convertible* with ``(a,b)``.  Similarly, abstractions *inside* a tuple are also still part of the case tree, and block reduction until applied to all their arguments: if we have

.. code-block:: none

   def unpairfn (f : A → B × C) : (A → B) × (A → C) ≔ (x ↦ (f x).fst, x ↦ (f x).snd)

then ``unpairfn f .fst`` does not reduce until applied to a further argument.  As with abstractions, you can force such reduction by wrapping the term in an identity function.


Eta-expansion and opacity
-------------------------

Often the behavior described above is convenient, e.g. when printing a term belonging to a large record type with many fields, such as ``ℤ : Ring`` or ``Grp : Cat``, you don't want to see the explicit definitions of all the fields.  However, there are times when you do want to see the definitions of the fields, and for this purpose you can change the "opacity" of a record type.

Opacity is an *attribute* of a record type.  Attributes are an experimental feature, particularly their syntax, and may change radically in the future.  At present, only record types can have attributes, and the only attributes are those relating to opacity.  The current syntax for defining a record type with an attribute is ``sig #(ATTR) ( … )``.  Currently attributes can only be set when a record type is defined; in the future it may be possible to alter them after the fact.  Opacity attributes do *not* affect convertibility of terms; η-conversion is always valid internally.  Opacity attributes only affect how terms are *displayed* to the user.  (If you want a record-like type without η-conversion, use a non-recursive codatatype; see :ref:`Codatatypes and comatching`.)

To explain the opacity attributes, suppose that with the definitions above, we also have

.. code-block:: none

   axiom x : A × ⊤
   def y : A × ⊤ ≔ (a, ⋆)
   def z : A × ⊤ ≔ (a, ())

We now list the opacity attributes, along with how altering the opacity of ``prod`` (but not ``⊤``) would change the printing behavior of the above terms.

- ``opaque``: This is the default setting, as described above: no η-expansion happens, so only terms that are syntactically tuples outside of a case tree are printed as tuples.  If ``prod`` is opaque, then:

   - ``x`` is printed as ``x``
   - ``y`` is printed as ``y``
   - ``z`` is printed as ``z``
- ``transparent``, a.k.a. ``transparent labeled``: When a record type is transparent, *all* terms belonging to that record type are η-expanded before being printed.  By default, η-expanded tuples are printed with labels; the alternate attribute name ``transparent labeled`` emphasizes this.  If ``prod`` is transparent labeled, then:

   - ``x`` is printed as ``(fst ≔ x .fst, snd ≔ x .snd)``
   - ``y`` is printed as ``(fst ≔ a, snd ≔ ⋆)``
   - ``z`` is printed as ``(fst ≔ a, snd ≔ z .snd)``.  Note that ``z .snd`` is not η-expanded to ``()`` because it belongs to the record type ``⊤`` which we are assuming is still opaque.
- ``transparent positional``: Like ``transparent labeled``, but η-expanded tuples are printed positionally rather than with labeled terms.  If ``prod`` is transparent positional, then:

   - ``x`` is printed as ``(x .fst, x .snd)``
   - ``y`` is printed as ``(a, ⋆)``
   - ``z`` is printed as ``(a, z .snd)``
- ``translucent``, a.k.a. ``translucent labeled``: When a record type is translucent, terms belonging to that record type are η-expanded before being printed if and only if they are a tuple in a case tree.  Note that this does not guarantee that all or any of their fields will evaluate completely; any field whose case tree branch is stuck will be printed as a projection, as in the transparent case.  If ``prod`` is translucent labeled, then:

   - ``x`` is printed as ``x``
   - ``y`` is printed as ``(fst ≔ a, snd ≔ ⋆)``
   - ``z`` is printed as ``(fst ≔ a, snd ≔ z .snd)``.
- ``translucent positional``: Like ``translucent labeled``, but η-expanded tuples are printed positionally rather than with labeled terms.  If ``prod`` is translucent positional, then:

   - ``x`` is printed as ``x``
   - ``y`` is printed as ``(a, ⋆)``
   - ``z`` is printed as ``(a, z .snd)``

For a record type with zero fields, η-expansion prints all of its elements as ``()``, with no difference between labeled and positional.  And for a record type with one field, positional η-expansion prints its elements as ``(_ ≔ a)``.  There is currently no way to cause the projections in an η-expansion to be printed with positional notation such as ``(x .0, x .1)``.
