Mutual definitions
==================

A block of constants can be defined mutually.  This means that first all of their *types* are checked, in order, so that the types of later constants in the block may refer to earlier constants (but using only their types, not their definitions).  Then their definitions are checked, again in order, so that the definitions of later constants may use the definitions of earlier ones (as well as the types of arbitrary ones).  Because canonical types are just a kind of definition, the same syntax for mutual definitions encompasses mutually recursive functions, mutually inductive types, inductive-inductive types, and even inductive-recursive types and functions.  Furthermore, all these kinds of mutual definitions can be encoded as single definitions using record-types (but the explicit mutual syntax is usually more congenial).

The syntax for a mutual block of definitions looks just like a sequence of ordinary ``def`` commands, except that the second and later ones use the keyword ``and`` instead of ``def``.  This is similar to the syntax of ML-like programming languages and Coq, and in contrast to Agda's style in which declarations and definitions can be mixed arbitrarily as long as each constant is declared before it is defined.  We prefer to keep the declaration of the type of each constant next to its definition, and make it clear textually which blocks of constants are defined mutually, at the price of allowing the definition of a constant to refer to others whose type is declared later textually in the same block.

An entire mutual block constitutes a single command, since it is impossible to typecheck any part of it individually.  It is nevertheless usual to put a blank line in between the definitions in a mutual block, although note that this cannot be done in interactive mode since a blank line ends the command.

Like any definition, the constants in a mutual block can be defined using the synthesizing form of ``def`` that omits their type.  However, this is of limited usefulness, since then they cannot be used while typechecking other constants in the block, as their types are not yet known at that point.

We now give a few examples to illustrate the possibilities of mutual definitions, along with their encodings using records.


Mutual recursion
----------------

We can define the Boolean predicates ``even`` and ``odd`` on the natural numbers:

.. code-block:: none

   def even : ℕ → Bool ≔ [
   | zero.  ↦ true.
   | suc. n ↦ odd n
   ]
   
   and odd : ℕ → Bool ≔ [
   | zero.  ↦ false.
   | suc. n ↦ even n
   ]

Thus, for instance, ``even 4`` reduces to ``true.``

Encoded as a single definition, this looks like the following.

.. code-block:: none

   def even_odd : (ℕ → Bool) × (ℕ → Bool) ≔ (
     [ zero. ↦ true.  | suc. n ↦ even_odd .1 n ],
     [ zero. ↦ false. | suc. n ↦ even_odd .0 n ])

Here we have used a binary product type, but in more complicated cases when doing such encoding, it may be helpful to define a custom record-type first in which the bundled family of mutually recursive functions lives.


Mutual induction
----------------

The Type-valued predicates ``Even`` and ``Odd`` can be defined similarly:

.. code-block:: none

   def Even : ℕ → Type ≔ data [
   | even_zero. : Even zero.
   | even_suc. : (n:ℕ) → Odd n → Even (suc. n)
   ]
   
   and Odd : ℕ → Type ≔ data [
   | odd_suc. : (n:ℕ) → Even n → Odd (suc. n)
   ]

Now ``Even 4`` doesn't reduce to anything, but it belongs to an indexed inductive type family, and can be inhabited by the term ``even_suc. 3 (odd_suc. 2 (even_suc. 1 (odd_suc. 0 even_zero.)))``.

The fact that canonical type declarations can appear as part of case trees means that these can also be encoded as a single definition:

.. code-block:: none

   def Even_Odd : (ℕ → Type) × (ℕ → Type) ≔ (
     data [
     | even_zero. : Even_Odd .0 zero.
     | even_suc. : (n:ℕ) → Even_Odd .1 n → Even_Odd .0 (suc. n) ],
     data [
     | odd_suc. : (n:ℕ) → Even_Odd .0 n → Even_Odd .1 (suc. n) ])


Recall that in Narya a third possibility is a recursive definition of families of canonical types:

.. code-block:: none

   def Even' : ℕ → Type ≔ [
   | zero. ↦ sig ()
   | suc. n ↦ sig (even_suc : Odd' n)
   ]
   and Odd' : ℕ → Type ≔ [
   | zero. ↦ data []
   | suc. n ↦ sig (odd_suc : Even' n)
   ]

In this case, ``Even' 4`` doesn't reduce to anything, but it is definitionally a singleton, with unique inhabitant ``(_ ≔ (_ ≔ (_ ≔ (_ ≔ ()))))``.


Inductive-inductive families
----------------------------

An inductive-inductive definition consists of several type families defined by mutual induction, of which the types of later ones may depend on the previous ones.  For example, here is a definition of the bare bones of the syntax of type theory (contexts and types) that often appears as an example of induction-induction:

.. code-block:: none

   def ctx : Type ≔ data [
   | empty.
   | ext. (Γ : ctx) (A : ty Γ)
   ]

   and ty (Γ : ctx) : Type ≔ data [
   | base.
   | pi. (A : ty Γ) (B : ty (ext. Γ A))
   ]

Note that the context Γ is a non-uniform parameter of the datatype ``ty``.  Here is its encoding as a single definition:

.. code-block:: none

   def ctx_ty : Σ Type (X ↦ (X → Type)) ≔ (
     ctx ≔ data [
     | empty.
     | ext. (Γ : ctx_ty .0) (A : ctx_ty .1 Γ) ],
     ty ≔ Γ ↦ data [
     | base.
     | pi. (A : ctx_ty .1 Γ) (B : ctx_ty .1 (ext. Γ A)) ])

Inductive-recursive definitions
-------------------------------

An inductive-recursive definition consists of one or more type families defined by induction together with one or more functions defined by recursion, in a way that refer to each other.  For instance, here is an inductive-recursive universe that contains the Booleans and is closed under Π-types:

.. code-block:: none

   def uu : Type ≔ data [
   | bool.
   | pi. (A : uu) (B : el A → uu)
   ]
   
   and el : uu → Type ≔ [
   | bool. ↦ Bool
   | pi. A B ↦ (x : el A) → el (B x)
   ]

Because a case tree can include canonical type declarations in some branches and ordinary (co)recursive definitions in other branches, we can also encode this as a single definition:

.. code-block:: none

   def uu_el : Σ Type (X ↦ (X → Type)) ≔ (
     uu ≔ data [
     | bool.
     | pi. (A : uu_el .0) (B : uu_el .1 A → uu_el .0) ],
     el ≔ [
     | bool. ↦ Bool
     | pi. A B ↦ (x : uu_el .1 A) → uu_el .1 (B x) ])

Mutually recursive let-bindings
-------------------------------

Mutual recursive families of local bindings can also be defined by following ``let rec`` with ``and``.  For instance, as a silly example we can define ``even`` without making ``odd`` globally visible:

.. code-block:: none

   def even (n : ℕ) : Bool ≔
     let rec even : ℕ → Bool ≔ [ zero. ↦ true. | suc. n ↦ odd n ]
     and odd : ℕ → Bool ≔ [ zero. ↦ false. | suc. n ↦ even n]
     in
     even n

Note that although the outer global ``def`` can (like any ``def``) refer to itself recursively, the locally-bound ``even`` shadows the global one, so that ``even`` in the final line refers to the local one.


Here be dragons
---------------

As can be seen from these examples, Narya's facility for mutual definitions is comparable to Agda's in flexibility and power.  Also like Agda, Narya currently permits even more radical things such as nested datatypes:

.. code-block:: none

   def Bush (A:Type) : Type ≔ data [
   | leaf.
   | cons. (_ : A) (_ : Bush (Bush A))
   ]

and poorly understood things such as mutual families of definitions including both inductive and coinductive types and both recursive and corecursive functions.  As noted above, we have not yet implemented positivity, termination, or productivity checkers, so it is easy to create inconsistencies even without these more radical features.  Eventually, we intend the default to be a "safe mode" that restricts mutual definitions to combinations that are known to be consistent and have understood semantics, although this could be turned off by a flag.

