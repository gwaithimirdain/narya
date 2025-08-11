Interactive proof
=================

Holes
-----

The basic ingredient of interactive proof is a *hole*.  A hole is indicated by the character ``?``, which is always its own token.  A hole does not synthesize, but checks against any type whatsoever.  A command containing one or more holes will succeed as long as all the terms in it typecheck without knowing anything about the contents of the holes, i.e. treating the holes as axioms generalized over their contexts, i.e. if it would be well-typed for *any* value of the hole having its given type.  If there are equality constraints on the possible fillers of the hole, then the command will fail; a hole is not equal to anything except itself (this may be improved in the future).

In practice, this restriction usually means that you cannot put a hole anywhere as a "dependent argument", i.e. where the output *type* of a function application depends on the *value* of the hole.  For instance, suppose given transitivity of equality in :ref:`Higher Observational Type Theory`:

.. code-block:: none

   concat (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z) : Id A x z

Then if you want to prove ``Id A a b``, you cannot write ``concat A ? ? ? ? ?`` and then go in and fill all the holes, because ``concat A ? ? ? ? ?`` has type ``Id A ? ?`` (specifically, the first and third ``?``) and Narya can't tell that this is equal to ``Id A a b`` with the holes unfilled, nor can it (currently) "wait to find out" what the holes will be filled with (this is called "postponing constraints").  But you can write ``concat A a ? b ? ?``, because the other three arguments of ``concat`` don't appear in its output type, so Narya can tell that ``concat A a ? b ? ?`` has type ``Id A a b`` regardless of what you may fill the holes with.

When a command containing holes finishes succesfully (in verbose or interactive mode), messages are emitted showing the type and context of every hole in it.  In ProofGeneral mode, these types and contexts are displayed in the "goals" window.  In the case of a ``def`` or an ``axiom`` command, you can continue to issue/process other commands afterwards, and each hole will continue to be treated like an axiom until you :ref:`solve it<Solving holes>`.  The commands ``echo`` and ``synth`` (including their ProofGeneral equivalents ``C-c :`` and ``C-c ;``) can also contain holes, whose types and contexts will still be displayed, but such holes are not saved after the command completes.

When a term containing a hole is printed, the hole displays as ``?N{…}`` where ``N`` is the sequential number of the hole.  (Note that even if no holes appear explicitly when you print a term, it might still depend implicitly on the values of holes if it involves constants whose definition contain holes.)  Unlike the printing of most terms, ``?N{…}`` for a hole is *not* a re-parseable notation.  Moreover, if the hole has a nonempty context, then occurrences of that hole in other terms may have other terms substituted for the variables in its context and these substitutions *are not indicated* by the notation ``?N{…}`` (this is what the notation ``{…}`` is intended to suggest).  This may be improved in future, but it is ameliorated somewhat by the treatment of holes in case trees.

Specifically, a hole ``?`` left in a place where a case tree would be valid to continue is a *case tree hole*, and is treated a bit differently than an ordinary hole.  The obvious difference is that a case tree hole can be solved (see :ref:`Solving holes`) by a case tree rather than an ordinary term.  But in addition, evaluation of a function does not reduce when it reaches a case tree hole, and thus a case tree hole will never appear when printing terms: instead the function in which it appears as part of the definition.  This may be a little surprising, but it has the advantage of being a re-parseable notation, and also explicitly indicating all the arguments of the function (which would constitute the substitution applied to a term hole, and hence not currently printed).

When Narya reaches the end of a file (or command-line ``-e`` string) in which any holes were created and not solved, it issues an error.  In the future this might become configurable, but it aligns with the behavior of most other proof assistants that each file must be complete before it can be loaded into another file.  Of course, this doesn't happen in interactive mode.  For this reason, a warning message is emitted after every command as long as there are open holes remaining.


Solving holes
-------------

Generally the purpose of leaving a hole is to see its displayed type and context, making it easier to *fill* the hole by a term.  The most straightforward way to fill a hole in a ``def`` or ``axiom`` command is to edit the source code to replace the ``?`` by a term (perhaps containing other holes) and reload the file.  In interactive mode, if you just entered a command containing a hole, you can ``undo 1`` to cancel the original command containing the hole, press Up-arrow or Meta+P to recover it in the history, edit it to replace the ``?``, and re-execute it.  And in ProofGeneral mode, you can use ``C-c C-u`` or ``C-c RET`` to retract the hole-creating command (along with any commands after it) and edit it (or just start editing it and it will auto-retract), and then re-process it with ``C-c C-n``.

It is also possible to fill a hole *without* retracting the command or any other commands after it.  When a command containing holes is processed using ProofGeneral, each hole ``?`` is replaced by a highlighted region delimited by the characters ``¿`` and ``ʔ``.  (The latter is the symbol for a glottal stop, which looks like a ``?`` but is distinct from it, allowing the region to contain other hole characters ``?``.  Normally you do not need to worry about typing or distinguishing these characters yourself, as they will be inserted automatically for holes that you create with an ordinary question mark.)  This region is editable, even though it is inside the processed region; it is provided for you to synthesize and evaluate terms in the context of the hole, and eventually solve the hole with one such term.  The commands ``C-c C-j`` and ``C-c C-k`` will move your cursor to the next or previous hole, respectively.  When the cursor is in a hole region, the following commands are available:

- ``C-c ,`` : Display the context and type of the current hole.  (The command ``C-c C-?``, available anywhere, displays the context and type of all open holes.)
- ``C-c SPC`` : Attempt to solve the current hole with the term written in the hole region.  Prompts for a term if the hole region is empty.  If this succeeds, the solving term will replace the current hole region, without retracting the original command or anything after it.
- ``C-c C-y`` : Split in the current hole on the term written in the hole region (or one prompted for).  See :ref:`Splitting in holes`.
- ``C-c :`` : Synthesize the type of the term written in the hole region in the context of that hole, prompting for confirmation or if the hole region is empty.  (Outside a hole region, this prompts for a term and synthesizes it in the global context.)
- ``C-c ;`` : Normalize the term written in the hole region in the context of that hole, prompting for confirmation or if the hole region is empty.  (Outside a hole region, this prompts for a term and normalizes it in the global context.)

The ability to solve holes with ``C-c SPC`` enables you to process a bunch of commands containing holes, some of which might be slow to run, and then progressively work on filling the holes in any desired order without having to retract and re-process anything.  Of course, the term that you fill a hole with contain other holes, which you can then successively solve.

Note that the term solving a hole is parsed and typechecked *in the context where the hole was created*.  Thus it can refer by name to variables that were in the context at that point and constants that were defined at that point, and use notations that were in effect at that point, but not constants or notations that were defined later.

In text-based interactive mode, you can solve a hole with the command ``solve``, identifying a particular hole by its number as in ``solve 0 ≔ X``.  (This is also the command issued by ProofGeneral under the hood when you use ``C-c C-SPC``.)  But identifying a hole by number is too brittle to use in a file, so this command is only allowed in text-based interactive mode.  You can likewise re-display the context and type of a hole by number with ``show hole HOLE``, or ``show holes`` which displays all currently open holes.


Multiple hole terms
-------------------

The command ``C-c :`` in a hole region allows you to test out different terms, or parts of terms, in the context of a hole, to help you figure out a term that will work to solve the hole.  However, sometimes it is helpful to be working simultaneously on several parts of such a term, such as a function and several of its arguments.  To assist with this, the character ``!`` (which is special and has no other meaning to Narya) in a hole region *subdivides* that region into multiple separate terms.  When there are one or more ``!`` characters in a hole region:

- The commands ``C-c :`` and ``C-c ;`` operate only on the contents of the current subdivision.
- The commands ``C-c SPC`` and ``C-c C-y`` prompt for which of the subdivisions' contents to use, or to concatenate them or enter an entirely new term.  If the command is successful, the contents of the unused subdivisions are discarded.

Note that the contents of a hole region can span multiple lines.  For visual clarity, it is recommended when working with multiple subdivisions that you place them on separate lines, with the dividing ``!`` characters at the beginning of each line.
 

Splitting in holes
------------------

Narya has a limited ability to infer the shape of a term to solve a hole with from the type of that hole or from the type of an argument to match against.  In ProofGeneral mode, if you position the cursor over a hole and type ``C-c C-y``, you will be prompted for a term on which to split (using the contents of the current hole as the default), or to leave it blank to split on the type of the goal.  (As a mnemonic for this command, the letter ``Y`` looks like a "split".)  Narya will then try to guess the shape of a term to fill the hole with, leaving additional holes in appropriate places.  You will be given the opportunity to edit the suggested term before it is used to solve the hole (for instance, to change the names of new variables being bound).  This includes:

- If you enter a term, that term must synthesize a datatype (see :ref:`Inductive datatypes and matching`).  The term inserted will then be a match against that term, with appropriate branches for all of its constructors.  The default variable names for the arguments of each constructor are taken from the datatype declaration, although you can change them when prompted with the term.  This includes higher-dimensional versions of data types (see :ref:`Id of datatypes`).  However, it is not currently possible to use this method to insert :ref:`Multiple matches and deep matches`.

- If you don't enter a term, and the hole has a function type, the term inserted will be an abstraction with a new hole in the body.  The variable names in the abstraction are taken from the function type, e.g. for ``(x : A) → B`` the term inserted will be ``x ↦ ?``.  For a function type with unnamed variable like ``A → B``, the variable inserted will be a placeholder ``_`` (which you will probably want to change when prompted to edit the term).  Iterated function-types like ``(x : A) (y : B) → C`` lead to iterated abstractions ``x y ↦ ?``, and higher-dimensional function-types like ``Id ((x : A) → B) f g`` lead to :ref:`Cubes of variables` ``x ⤇ ?``.

- If you don't enter a term, and the hole has a record type (see :ref:`Record types and tuples`), the term inserted will be a tuple with all fields labeled such as ``(fst ≔ ?, snd ≔ ?)``.  This includes higher-dimensional versions of record types (see :ref:`Id of record types`).

- If you don't enter a term, and the hole has a codata type (see :ref:`Codatatypes and comatching`), including higher-dimensional versions thereof, the term inserted will be a comatch such as ``[ .head ↦ ? | .tail ↦ ? ]``.  This also works with :ref:`higher coinductive types`: the correct number of copies of each higher field are inserted depending on the dimension of the type.

- If you don't enter a term, and the hole has a data type (see :ref:`Inductive datatypes and matching`) that has exactly one constructor, the term inserted will be an application of that constructor such as ``constr. ? ? ?``.  This includes higher-dimensional versions of data types (see :ref:`Id of datatypes`).

If none of these cases apply, an error results.

Note that the term generated by a split is not guaranteed to typecheck.  For example, if the goal is an indexed datatype with one constructor, splitting will generate an application of that constructor to holes; but if the indices depend at all on the arguments of the constructor, this will not typecheck since Narya will be unable to tell whether the indices agree with those of the goal.  More mundanely, if a datatype constructor is declared with multiple arguments of the same name such as ``data [ constr. (x:A) (x:A) ]`` (I don't know why you would do that, but it's allowed with the second ``x`` shadowing the first), splitting on a term of that type will generate a match such as ``match u [ constr. x x ↦ ? ]``, which fails to typecheck because the pattern variables in each branch of a match are required to be distinct.

You can also split on a hole directly in interactive mode, identifying a hole by its number as in ``split 0 ≔ M`` to split on a term ``M``, or ``split 0 ≔ _`` to split on the goal type.  This will print the proposed term with the label "hole could be solved by"; you can then copy it, edit it as desired, and supply it to a ``solve`` command.


Undoing solved holes
--------------------

Solving a hole cannot be "undone" by Narya; it happens "outside the timestream", effectively altering a previously executed command rather than executing a new one, and does not affect the sequence of commands available to be undone.  This should be intuitive in ProofGeneral, where solving a hole does not change the processed region or insert any commands in the buffer, and a subsequent "undo" (``C-c C-u``) acts on the most recently processed command *in the buffer* whether or not that was the command containing the solved hole.  For example, suppose you process a command defining ``f`` that contains a hole, then process another command defining ``g``, then solve the hole in the definition of ``f``.  After this, an "undo" will retract the definition of ``g``, leaving the definition of ``f`` with its solved hole in place.
 
Along the same lines, undoing commands in ProofGeneral does not affect the replacement of holes by the terms that solve them in the text of the buffer.  Thus, if you process a command containing a hole, solve the hole, and then undo *that* command, the term with which you solved the hole remains in the buffer in place of the original ``?``.  Therefore, if you then re-process the command, the solving term will be used where there used to be a hole, without creating a hole at all.  For purposes of later commands, this should be entirely equivalent to continuing on with a filled hole (although it is not *literally* identical in Narya's internals, so bugs may exist; if you find one, please report it).

On the other hand, solving a hole changes the text of the Emacs buffer, and therefore it *can* be un-done with *Emacs's* ``undo`` command (generally bound to ``C-/``, ``C-_``, and ``C-x u``), removing the inserted term and replacing the ``¿...ʔ`` region.  Since the "solve" command cannot be undone by Narya, if you undo it in Emacs there is no consistent thing that Narya can do with the command containing that hole.  Thus, in this case the Narya ProofGeneral mode automatically also retracts the processed region past the command containing the hole.


Reformatting solved holes
-------------------------

By default, when filling a hole interactively with ProofGeneral, the term you enter is automatically reformatted.  In particular, line breaks and indenting spaces are inserted in (what Narya thinks are) appropriate places (and removed from what it thinks are inappropriate places), and ASCII operators such as ``->`` and ``|->`` are replaced by their Unicode equivalents such as → and ↦.  Unfortunately, at present the solving term is reformatted entirely on its own without reference to the command in which it appears, so after it is inserted the overall command may still be badly formatted, especially if you inserted a case tree structure such as ``match``.  Currently the only solution to this is to retract the command after solving the hole and then re-process it to reformat it.

As with reformatting of commands and source files, reformatting of hole-solving terms is affected by the command-line flags ``-unicode`` and ``-ascii`` (print operators as → or ``->``, respectively).  You can also turn off solve-reformatting entirely by setting the Emacs customization variable ``narya-reformat-holes`` to ``nil``.  However, if you don't like the way Narya reformats your terms, I would appreciate it if you give me feedback about it rather than (or, at least, in addition to) turning it off.
