Imports and scoping
===================

File imports
------------

The command ``import FILE`` executes another Narya file and adds (some of) its definitions and notations to the current namespace.  The commands in the imported file cannot access any definitions from other files, including the current one, except those that it imports itself.  Importing is not transitive: if ``a.ny`` imports ``b.ny``, and ``b.ny`` imports ``c.ny``, then the definitions from ``c.ny`` do not appear in the namespace of ``a.ny`` unless it also imports ``c.ny`` explicitly.

More precisely, there are two namespaces at any time: the "import" namespace, which determines the names that are available to use in the current file, and the "export" namespace, which determines the names that will be made available to other files that import this one.  The command ``import`` only affects the import namespace, but the variant using the word ``export`` instead affects both.

By contrast, when in interactive mode or executing a command-line ``-e`` string, all definitions from all files and strings that were explicitly specified previously on the command line are available, even if not exported.  This does not carry over transitively to files imported by them.  Standard input (indicated by ``-`` on the command line) is treated as an ordinary file; thus it must import any other files it wants to use, but its definitions are automatically available in ``-e`` strings and interactive mode.

No file will be executed more than once during a single run, even if it is imported by multiple other files.  Thus, if both ``b.ny`` and ``c.ny`` import ``d.ny``, and ``a.ny`` imports both ``b.ny`` and ``c.ny``, any effectual commands like ``echo`` in ``d.ny`` will only happen once, there will only be one copy of the definitions from ``d.ny`` in the namespace of ``a.ny``, and the definitions from ``b.ny`` and ``c.ny`` are compatible.  Circular imports are not allowed (and are checked for).  The order of execution is as specified on the command-line, with depth-first traversal of import statements as they are encountered.  Thus, for instance, if the command-line is ``narya one.ny two.ny`` but ``one.ny`` imports ``two.ny``, then ``two.ny`` will be executed during ``one.ny`` whenever that import statement is encountered, and then skipped when we get to it on the command-line since it was already executed.

Namespaces and sections
-----------------------

Narya uses `Yuujinchou <https://redprl.org/yuujinchou/yuujinchou/>`_ for hierarchical namespacing, with periods to separate namespaces.  Thus a name like ``nat.plus`` lies in the ``nat`` namespace.  You can define a constant with such a name explicitly:

.. code-block:: none
   
   def nat.plus ≔ BODY

According to Yuujinchou, namespaces are untyped, implicit, and patchable: you can add anything you want to the ``nat`` namespace, anywhere, simply by defining it with a name that starts with ``nat.``

In addition, the ``section`` command allows defining a group of constants without an explicit namespace, but with a given prefix added to their names afterwards.  For example, an equivalent way of defining ``nat.plus`` would be:

.. code-block:: none

   section nat ≔
     def plus ≔ BODY
   end

All ordinary commands are valid inside a section, including other section commands.  When a section is closed with ``end``, all the constants that were defined in that section are prefixed by the name of that section and merged into the outer namespace (which might itself be another section, and so on).

Like a file, a section has both a visible namespace and an export namespace, and ``import`` statements in a section only affect the visible namespace.  Thus, imported names are no longer visible after the section is closed.  But as with importing files, if you use ``export`` instead inside a section, then the imported names are placed in export namespace; thus when the section is closed they are treated like constants defined in the section and are merged into the outer namespace with the section name prefix.


Import modifiers
----------------

By default, an ``import`` command merges the namespace of the imported file with the current namespace.  However, it is also possible to apply Yuujinchou *modifiers* to the imported namespace before it is merged with the command form ``import FILE | MOD``.  (The symbol ``|`` is intended to suggest a Unix pipe that sends the definitions of ``FILE`` through the modifiers before importing them.)  The valid modifiers are exactly the `Yuujinchou modifiers <https://redprl.org/yuujinchou/yuujinchou/Yuujinchou/Language/index.html#modifier-builders>`_:

- ``all``: Keep everything, checking that there is something to keep.
- ``id``: Keep everything, without checking that there is anything to keep.
- ``none``: Drop everything, checking that there was something to drop.
- ``only NAME``: Keep only the namespace rooted at ``NAME``, without renaming anything.  Thus ``only nat`` will keep ``nat.plus`` and ``nat.times``, under those names, but discard ``int.plus``.
- ``except NAME``: Keep everything except the namespace rooted at ``NAME``, without renaming anything.  Thus ``except nat`` will discard ``nat.plus`` and ``nat.times`` but keep ``int.plus`` and ``real.plus``.
- ``in NAME MOD``: Apply the modifier ``MOD`` to the namespace rooted at ``NAME``, leaving everything else alone.  Thus ``in nat only plus`` will keep ``nat.plus.assoc`` and ``nat.plus.comm`` and ``int.times`` but discard ``nat.times.assoc``.
- ``renaming NAME1 NAME2``: Rename the namespace rooted at ``NAME1`` to instead be rooted at ``NAME2``, checking that ``NAME1`` is nonempty, and silently dropping anything already present under ``NAME2``.
- ``seq (MOD1, MOD2, …)``: Perform the modifiers ``MOD1``, ``MOD2``, and so on in order.  In particular, ``seq ()`` is equivalent to ``id``.
- ``union (MOD1, MOD2, …)``: Apply all the modifiers ``MOD1``, ``MOD2`` to the original namespace in parallel and take the union of the results.  In particular, ``union ()`` is like ``none`` but doesn't check that there is anything to drop.

The ``NAME`` s in all these commands are ordinary identifiers, with one additional option: a bare period ``.`` represents the root namespace.  Thus ``renaming nat .`` will rename ``nat.plus`` to just ``plus`` and ``nat.times`` to just ``times``, discarding everything that doesn't start with ``nat``.  On the other hand, ``renaming . foo`` will add ``foo`` to the beginning of everything.  In particular, therefore, ``import "arith" | renaming . arith`` is the standard sort of "qualified import" that will import definitions like ``nat.plus`` from a file like ``arith.ny`` but renamed to ``arith.nat.plus``.

Currently, you can and must specify explicitly the qualifying namespace prefix; it has no automatic relationship to the imported filename or path.  More generally, the full syntax for Yuujinchou modifiers is rather verbose, so we may introduce abbreviated versions of some common operations.  Feedback is welcome about what those should be.


Importing namespaces
--------------------

The first argument of the ``import`` command can also be a namespace, with the effect that the contents of that namespace are merged with the root, possibly with a modifier applied.  Thus, for instance, after the following:

.. code-block:: none
   
   axiom a.one : ℕ ≔ 1
   axiom a.two : ℕ ≔ 2
   import a | renaming one uno

the names ``a.one`` and ``uno`` will refer to ``1`` while the names ``a.two`` and ``two`` will refer to ``2``.

Imported names also remain available in their original locations; there is no way to remove a name from the scope once it is added.  In addition, names imported this way are not *exported* from the current file when it it loaded by another file.  That is, if the above example is in a file ``foo.ny``, then if some other file says ``import "foo"`` then it will only be able to access the original names ``a.one`` and ``a.two``, not the new ones ``uno`` and ``two``.  But, of course, they are exported if the variant called ``export`` is used instead.


Importing notations
-------------------

Visibility of notations defined by another file, or in a section, is implemented as a special case of importing names.  Specifically, when a new notation is declared, it is associated to a name in the current namespace prefixed by ``notations``.  The name is obtained from its pattern by replacing variables with underscores, concatenating them with the symbols (unquoted) separated by spaces, and surrounding it in guillemets ``«»`` to make it an atomic identifier.  Thus, for instance, ``notation(1) x "+" y ≔ plus x y`` associates this notation to the name ``notations.«_ + _»``.

Then, whenever another file or section is imported, any notations that are present in the ``notations`` namespace after the modifiers are applied become available in the current file.  Since by default the complete namespace of an imported file is merged with the current one, this means that by default all notations defined in that file also become available.

The ``notations`` namespace is not otherwise special: you can put constants in it too, but this is not recommended.  The names of constants and of notations inhabit the same domain: you cannot have a constant and a notation with the same name, although since newly created notations always have names autogenerated from their patterns and starting with ``notations`` this is not usually a problem.  It is possible for notations to end up with names that don't start with ``notation`` through import modifiers, but in that case they are not available to the parser.

For example, you can avoid making any imported notations available by using the modifier ``except notations``, or you can import only the notations and no definitions with ``only notations``.  Or you can import only a few particular notations with a modifier like ``in notations union (only «_ + _»; only «_ * _»)``.  In particular, if you import an entire file qualified such as ``import "arith" | renaming . arith``, then a notation such as ``notations.«_ + _»`` in ``"arith.ny"`` will be renamed to ``arith.notations.«_ + _»``, which is not in the ``notations`` namespace and thus will not be available to the parser.  To import all the constants qualified but make all the notations available, you can use one of the following.

.. code-block:: none

   import "arith" | seq (renaming . arith, renaming arith.notations notations)
   import "arith" | union (renaming . arith, only notations)

Similarly, notations that are defined inside a section named ``nat`` will appear outside that section in the namespace ``nat.notations``.  Since this is not in the global ``notations`` namespace, these notations will no longer be in effect after the section is closed.  You can bring them into the global scope, while keeping definitions from the section qualified, by issuing the following command after the section closes.

.. code-block:: none

   import nat | only notations

You can also put them into a sub-namespace of ``notations`` with a command like this:

.. code-block:: none

   import nat | seq (only notations, renaming notations notations.nat)

Notations in sub-namespaces of ``notations`` still have an effect on printing and parsing, so there is not much difference between these two for purposes of the present file.  However, if you change ``import`` to ``export`` in the above two statements, then users who import the current file will also get these notations by default.  But with the second option, these users will also be able to choose to import *only* the ``nat`` notations with ``in notations only nat``, or all notations except the ``nat`` notations with ``in notations except nat``.  Thus, sub-namespaces of ``notations`` act somewhat like Rocq's `notation scopes <https://rocq-prover.org/doc/V9.0.0/refman/user-extensions/syntax-extensions.html#notation-scopes>`_, although they can (currently) only be opened globally, and not locally to part of a term.


Compilation
-----------

Whenever a file ``FILE.ny`` is successfully executed, Narya writes a "compiled" version of that file in the same directory called ``FILE.nyo``.  Then in future runs of Narya, whenever ``FILE.ny`` is to be executed, if

1. ``-source-only`` was not specified,
2. ``FILE.ny`` was not specified explicitly on the command-line (so that it must have been imported by another file),
3. ``FILE.nyo`` exists in the same directory,
4. the same type theory flags (``-arity``, ``-direction``, ``-internal``/``-external``, and ``-discreteness``) are in effect now as when ``FILE.nyo`` was compiled,
5. ``FILE.ny`` has not been modified more recently than ``FILE.nyo``, and
6. none of the files imported by ``FILE.ny`` are newer than it or their compiled versions,

then ``FILE.nyo`` is loaded directly instead of re-executing ``FILE.ny``, skipping the typechecking step.  This can be much faster.  If any of these conditions fail, then ``FILE.ny`` is executed from source as usual, and a new compiled version ``FILE.nyo`` is saved, overwriting the previous one.

Effectual commands like ``echo`` are *not* re-executed when a file is loaded from its compiled version (they are not even stored in the compiled version).  Since this may be surprising, Narya issues a warning when loading a compiled version of a file that originally contained ``echo`` commands.  Since files explicitly specified on the command-line are never loaded from a compiled version, the best way to avoid this warning is to avoid ``echo`` statements in "library" files that are intended to be imported by other files.  Of course, you can also use ``-source-only`` to prevent all loading from compiled files.
