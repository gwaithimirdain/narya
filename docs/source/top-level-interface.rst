Top level interface
===================


Command-line flags
------------------

The Narya executable accepts at least the following command-line flags.

Execution behavior
^^^^^^^^^^^^^^^^^^

- ``-interactive`` or ``-i``: Enter interactive mode (see :ref:`Execution`)
- ``-exec STRING`` or ``-e STRING``: Execute a string argument (see :ref:`Execution`)
- ``-source-only``: Load all files from source, ignoring any compiled versions

Formatting output
^^^^^^^^^^^^^^^^^

- ``-verbose`` or ``-v``: Show verbose messages
- ``-unicode`` and ``-ascii``: Display and reformat code using Unicode (default) or ASCII
- ``-no-reformat``: Do not automatically reformat source files (see :ref:`Code formatter`)
- ``-show-function-boundaries``: Display boundaries of functions, when implicit (see :ref:`Implicit boundaries`)
- ``-hide-function-boundaries``: Hide boundaries of functions, when implicit
- ``-show-type-boundaries``: Display boundaries of functions, when implicit
- ``-hide-type-boundaries``: Hide boundaries of functions, when implicit

Controlling parametricity
^^^^^^^^^^^^^^^^^^^^^^^^^

These options are discussed under :ref:`Observational higher dimensions`, :ref:`Parametricity`, and :ref:`Higher Observational Type Theory`.

- ``-arity N``: Set the arity of parametricity to N (1 ≤ N ≤ 9)
- ``-direction X``: Set the symbol and names for reflexivity
- ``-internal`` and ``-external``: Set whether parametricity is internal (default) or external
- ``-discreteness``: Enable strictly parametrically discrete types
- ``-dtt``: Poor man's dTT mode (``-arity 1 -direction d -external``)
- ``-hott``: Higher Observational Type Theory mode

Execution
---------

When the Narya executable is run, it loads all the files given on its command line and any strings supplied on the command line with ``-e``.  As usual, the special filename ``-`` refers to standard input.  Files and strings are loaded in the order they are given on the command line; all files must have the extension ``.ny``.  Lastly, if ``-i`` was given anywhere on the command line, Narya enters interactive mode.

In interactive mode, commands typed by the user are executed as they are entered.  Since many commands span multiple lines, Narya waits for a blank line before parsing and executing the command(s) being entered.  Make sure to enter a blank line before starting a new command; interactive commands must be entered and executed one at a time.  The result of the command is printed (more verbosely than is usual when loading a file) and then the user can enter more commands.  Type Control+D to exit interactive mode, or enter the command ``quit``.  In addition, in interactive mode you can enter a term instead of a command, and Narya will assume you mean to :ref:`echo<Echo/Synth>` it.


Commands
------------

In a file, conventionally each command begins on a new line, but this is not technically necessary since each command begins with a keyword that has no other meaning.  (Similarly, a command-line ``-e`` string may contain multiple commands as long as whitespace separates them.)  Indentation is not significant, but there is a built-in :ref:`code formatter` that is on by default, enforcing a uniform indentation style.  The available commands in a file or ``-e`` string are the following.

Def
^^^

.. code-block:: none

   def NAME [PARAMS] [: TYPE] ≔ TERM [and ...]

Define a global constant called ``NAME`` having type ``TYPE`` and value ``TERM``.  Thus ``NAME`` must be a valid identifier (see :ref:`Identifiers`), while ``TYPE`` must parse and typecheck as a type, and ``TERM`` must parse and typecheck at type ``TYPE``.  If ``TYPE`` is omitted, then ``TERM`` must synthesize a type (see :ref:`synth<Echo/Synth>`).  In addition, if ``TYPE`` is specified, then ``TERM`` can also be a case tree or canonical type declaration (see :ref:`canonical types<Canonical types defined by case trees>`).

The optional ``PARAMS`` is a list of parameters of the form ``(x : PTY)``, or more generally ``(x y z : PTY)``, with the effect that the actual type of the constant ``NAME`` is the iterated function-type with these parameters as domain and ``TYPE`` (or the synthesized type of ``TERM``) as codomain, and its value is the λ-abstraction of ``TERM`` over them.  That is, ``def foo (x:A) : B ≔ M`` is equivalent to ``def foo : A → B ≔ x ↦ M``.

A family of constants can be defined mutually by using the ``and`` keyword to introduce the second and later ones (see :ref:`mutual definitions<Mutual definitions>`).

If ``NAME`` already has a definition that will be exported from the current scope, a warning about redefinition is emitted.

Axiom
^^^^^

.. code-block:: none

   axiom NAME [PARAMS] : TYPE

Assert a global constant called ``NAME`` having type ``TYPE``, without any definition (an axiom).  Parameters and names are treated as for ``def``.

Echo/Synth
^^^^^^^^^^

.. code-block:: none

   echo TERM

Normalize ``TERM`` and print its value and its type to standard output.  Note that ``TERM`` must synthesize a type (see :ref:`Bidirectionality`); if it is a checking term you must ascribe it.  In interactive mode, if you enter a term instead of a command, Narya assumes you mean to ``echo`` that term.

.. code-block:: none

   synth TERM

Like ``echo``, but does not normalize the term, only computes its type.

Notation
^^^^^^^^

.. code-block:: none

   notation [(TIGHTNESS)] […] PATTERN […] ≔ HEAD ARGUMENTS

Declare a new mixfix notation; see :ref:`Mixfix notations`.


Import/export
^^^^^^^^^^^^^

.. code-block:: none

    import "FILE"
    import "FILE" | MOD
  
Add the extension ``.ny`` to the double-quoted string ``FILE`` and import the file at that location (either absolute or relative to the location of the current file), with the optional modifier ``MOD`` applied to its namespace (see :ref:`Imports and scoping`).  The disk file *must* have the ``.ny`` extension, whereas the string given to ``import`` must *not* have it; this is because in the future the string given to ``import`` will be a more general "library identifier" in the `bantorra <https://redprl.org/bantorra/bantorra/index.html>`_ framework.

.. code-block:: none

    import NAME
    import NAME | MOD

Import the namespace rooted at ``NAME`` into the current top-level namespace, with the optional modifier ``MOD`` applied to it first.

.. code-block:: none

    export "FILE"
    export "FILE" | MOD
    export NAME
    export NAME | MOD
  
Same as above, but also export the new names to other files that import this one.

Sections
^^^^^^^^

.. code-block:: none

   section NAME ≔
   
Begin a section named ``NAME``, which must be a valid identifier.  All ordinary commands are valid inside a section (including other section commands).
   
.. code-block:: none

   end

End the section that was most recently opened and not yet closed.  All the constants that were in the export namespace of that section (i.e. those defined with ``def`` and ``axiom`` or imported from elsewhere with ``export``) are prefixed by the name of that section and merged into the previous namespace.  (See :ref:`Namespaces and sections`.)


Quit
^^^^

.. code-block:: none

   quit

Terminate execution of the current compilation unit.  Whenever this command is found, loading of the current file or command-line string ceases, just as if the file or string had ended right there.  Execution then continues as usual with any file that imported the current one, with the next file or string on the command line, or with interactive mode if that was requested.  The command ``quit`` in interactive mode exits the program (you can also exit interactive mode by typing Control+D).

Interactive commands
--------------------

In interactive mode, the following additional commands are also available.  (However, they are mostly intended for use by the :ref:`ProofGeneral mode`.)

Show hole(s)
^^^^^^^^^^^^

.. code-block:: none

    show hole HOLE
    show holes

Display the context and type of a specific open hole number ``HOLE``, or of all the open holes (see :ref:`Interactive proof`).

Solve/Split
^^^^^^^^^^^

.. code-block:: none

   solve HOLE ≔ TERM
   split HOLE ≔ TERM

Fill hole number ``HOLE`` with the term ``TERM`` or a split deduced from ``TERM`` and/or its type (see :ref:`Interactive proof`).

Undo
^^^^

.. code-block:: none

   undo N

Undo the last ``N`` commands that modify the global state, rewinding to a previous situation.  This includes all commands except ``echo``, ``synth``, ``show``, ``solve``, ``split``, and ``display``: those commands are skipped over when undoing.  (Of course ``solve`` does modify the global state, but it is not undoable because it doesn't affect the "processed position" in ProofGeneral; it exists "outside the timestream".)  The command ``undo`` itself is also not "undoable" and there is no "redo": after a command is undone, it is lost permanently from Narya's memory (although you can press Up-arrow or Meta+P to find it in the interactive history and re-execute it).  Following an ``undo`` with another ``undo`` will just undo additional commands: ``undo 1`` followed by ``undo 1`` is the same as ``undo 2``.

Display
^^^^^^^

.. code-block:: none

   display NAME ≔ VALUE

Set one of the display settings (that are also set by command-line flags).  Possible display settings are
   
.. code-block:: none

    display chars ≔ unicode
    display chars ≔ ascii
    display chars ≔ toggle
    display function boundaries ≔ on
    display function boundaries ≔ off
    display function boundaries ≔ toggle
    display type boundaries ≔ on
    display type boundaries ≔ off
    display type boundaries ≔ toggle


ProofGeneral mode
-----------------

`ProofGeneral <https://proofgeneral.github.io/>`_ is a generic development environment designed for proof assistants that runs inside the text editor Emacs.  Proof General is perhaps best known for its use with `Rocq <https://rocq-prover.org/>`_.  Narya comes with a basic ProofGeneral mode.  Narya does not yet have a true interactive *proof* mode, which ProofGeneral is designed for, but it is still useful for progressive processing of commands in a file.  In addition, the Narya ProofGeneral mode is enhanced with commands for creating, inspecting, and filling holes, similar to Agda's Emacs mode.

Basic usage
^^^^^^^^^^^

Once Narya's ProofGeneral mode is installed either :ref:`automatically<Automatic ProofGeneral installation>` or :ref:`manually<Manual ProofGeneral installation>`, it should start automatically when you open a file with the ``.ny`` extension.  When ProofGeneral mode is active, there is some initial segment of the buffer (which starts out empty) that has been processed (sent to Narya) and is highlighted with a background color (usually blue).  The unprocessed part of the buffer can be freely edited, and as you complete new commands you can process them as well one by one.  You can also undo or "retract" processed commands, removing them from the processed region.  If you edit any part of the processed region (except for editing inside an existing comment, or :ref:`filling a hole<solving holes>` with ``C-c C-SPC``), it will automatically be retracted (using Narya's ``undo`` command) up to the point where you are editing.

In addition to the main window displaying your source file, there will normally be two other windows in split-screen labeled "goals" and "response" (although this can be customized with the Emacs variables ``proof-three-window-enable`` and ``proof-three-window-mode-policy``).  The "response" window displays Narya's informational and error messages.  The "goals" window displays the contexts and types of holes whenever relevant.

Key commands
^^^^^^^^^^^^

The most useful ProofGeneral key commands for Narya are the following.  As usual in Emacs (see the `Emacs manual <https://www.gnu.org/software/emacs/manual/html_node/emacs/User-Input.html>`_), ``C-a`` means hold down the Control key and press ``a``, then release both.  Similarly, ``C-M-a`` means hold down both Control and Meta (Meta is usually the same as "Alt") and press ``a``, then release them all.

- ``C-c C-n`` : Process the next unprocessed command.  Since Narya has no command-terminating string, the "next command" is interpreted as continuing until the following command keyword or until the end of the buffer.  This means that if you've written a complete command but there is garbage following it, in order to process the command you'll need to either comment out the garbage or insert at least the beginning of another command in between (such as ``quit``) so that ProofGeneral can find the end of the command you want to process.
- ``C-c C-u`` : Retract the last processed command.
- ``C-c RET`` : Move the processed/unprocessed boundary to (approximately) the current cursor location, processing or retracting as necessary.
- ``C-c C-b`` : Process the entire buffer.
- ``C-c C-r`` : Retract the entire buffer.
- ``C-c C-.`` : Move the cursor to the end of the processed region.
- ``C-M-a`` : Move the cursor to the beginning of the command it is inside.
- ``C-M-e`` : Move the cursor to the end of the command it is inside.
- ``C-c C-v`` : Read a "state-preserving" command from the minibuffer and execute it, displaying its output in the result buffer.  Currently the only state-preserving commands are ``echo``, ``synth``, ``show``, and ``display``.
- ``C-c C-c`` : Interrupt Narya if a command is taking too long.  Narya attempts to recover, but its state may be unreliable afterwards.
- ``C-c C-x`` : Retract the buffer and kill the Narya subprocess.
- ``M-;`` : Insert a comment, remove a comment, or comment out a region.  This is a standard Emacs command, but is customized to use line comments on code lines and block comments elsewhere.

As noted above, Narya's ProofGeneral mode is enhanced to deal with open holes (see :ref:`Interactive proof`).  Whenever a hole is created by processing a command, the location of the hole is highlighted in ``narya-hole-face`` (which you can customize).  These highlights are removed when hole-creating commands are retracted.

Narya's ProofGeneral mode also defines the following additional key commands.

- ``C-c ;`` : Read a term from the minibuffer and normalize it (like ``C-c C-v`` with ``echo``), perhaps in the context of the current hole.
- ``C-c :`` : Read a term from the minibuffer and synthesize its type (like ``C-c C-v`` with ``synth``), perhaps in the context of the current hole.
- ``C-c C-?`` : Show the contexts and types of all open holes (like ``C-c C-v`` with ``show holes``).
- ``C-c C-,`` : Show the context and type of the hole under point (like ``C-c C-v`` with ``show hole``, except that you don't need to know the hole number).
- ``C-c C-j`` : Move the cursor to the position of the next open hole.
- ``C-c C-k`` : Move the cursor to the position of the previous open hole.
- ``C-c C-SPC`` : Fill the hole under point with a specified term, without retracting any code.
- ``C-c C-y`` : Split in the hole under point based on its type.
- ``C-c C-d C-u``: Toggle display of unicode characters.
- ``C-c C-d C-f``: Toggle display of function boundaries.
- ``C-c C-d C-t``: Toggle display of type boundaries.

For Agda users
^^^^^^^^^^^^^^
 
Agda users should beware: while a few of Narya's key commands are chosen to match those of Agda (like ``C-c C-?`` and ``C-c C-SPC`` and ``C-c C-,``), many of the key sequences used by Agda have already been defined in ProofGeneral to mean something else (notable examples are ``C-c C-n`` and ``C-c C-b`` and ``C-c C-.``), leading Narya to choose different ones.  For reference, here is a mapping of Agda keybindings to approximately comparable Narya ones:
 
- Instead of ``C-c C-l``, use ``C-c C-b`` (process the whole buffer).
- Instead of ``C-c C-f``, use ``C-c C-j`` (move to the next hole).
- Instead of ``C-c C-b``, use ``C-c C-k`` (move to the previous hole).
- Instead of ``C-c C-n``, use ``C-c ;`` (normalize a term, perhaps in hole context).
- Instead of ``C-c C-d``, use ``C-c :`` (synthesize a term, perhaps in hole context).
- Instead of ``C-c C-.``, use ``C-c :``  (synthesize a term) and ``C-c C-,`` (display hole context).
- Instead of ``C-c C-r``, use ``C-c C-y`` (split in a hole).
- Instead of ``C-c C-c``, use ``C-c C-y`` (split in a hole).
- Instead of ``C-c C-x C-q``, use ``C-c C-x`` (quit Narya subprocess).
- Instead of ``C-c C-x C-a``, use ``C-c C-c`` (interrupt a command).
 
If there is significant demand, we could implement a configuration option that instead preferentially chooses Agda's key bindings, moving the conflicting ProofGeneral bindings to other key sequences.

Syntax highlighting
^^^^^^^^^^^^^^^^^^^

Narya's ProofGeneral mode uses Emacs' font-lock system for syntax highlighting.  This is only approximately correct as it uses simple regexps, but it's fairly good, and can highlight code that hasn't been processed yet and wouldn't even parse.  It uses the following Emacs "faces", which you may want to customize, particularly because some of them are not configured by default to have any noticable color.

- ``font-lock-keyword-face``: commands such as ``def`` and ``axiom``.
- ``font-lock-builtin-face``: keywords such as ``let`` and ``match``.
- ``font-lock-function-name-face``: names of constants currently being defined or assumed.
- ``font-lock-constant-face``: constructor names.
- ``font-lock-number-face``: numerals.  I suggest making this face look the same as ``font-lock-constant-face``, since numerals are just a shorthand for constructor sequences.
- ``font-lock-property-name-face``: field and method names.
- ``font-lock-variable-name-face``: variables currently being bound by abstractions, let-bindings, as parameters, in the domains of dependent function-types, etc.
- ``font-lock-bracket-face``: parentheses, brackets, and braces.  Note that this inherits by default from ``font-lock-punctuation-face``.
- ``font-lock-operator-face``: single-character operators like → and ASCII operators such as ``->``.

ProofGeneral also uses some of its own faces that you may want to customize, such as the following.

- ``proof-locked-face``: the background highlight of the processed region.

And Narya defines some of its own faces as well.

- ``narya-hole-face``: the background highlight of open holes.


Code formatter
--------------

Narya comes with an "opinionated code formatter" like `gofmt <https://go.dev/blog/gofmt>`_, `ocamlformat <https://github.com/ocaml-ppx/ocamlformat>`_, or `prettier <https://prettier.io/docs/why-prettier>`_.  In fact, the formatter is built into Narya, using the same parser and pretty-printer as the typechecker; so they should never get out of sync as the language changes.

There are currently two ways to use the formatter.  Firstly, every time you run Narya on a source file, it automatically reformats that file.  (It only reformats files supplied explictly on the command line, not other files loaded by these.)  If this resulted in any changes, it copies the original file to a backup file with a ``.bak.N`` extension; this is a temporary feature to ensure you can recover your code in case of bugs in the reformatter, and will probably go away once there is enough evidence that the reformatter is trustworthy.  (Please report any bugs in the reformatter, especially serious ones that change the meaning of the code, make it non-reparseable, lose comments, etc.!  Also, reformatting is supposed to be idempotent: if reformatting code twice without editing it in the middle makes any changes the second time, that is also a bug.)

Secondly, every time you process a command in ProofGeneral, that command is automatically reformatted.  If you retract the command, it remains reformatted.  To undo the reformatting, you can use Emacs' undo operation (``C-/``); this will also retract the command, if it is still in the processed region.

Processing an entire file in ProofGeneral does not have *exactly* the same reformatting effect as running Narya on it from the command line.  They should reformat individual commands in the same way, but the command-line reformatter also ensures that distinct commands are separated by single blank lines (suitably interpreted in the presence of comments).  ProofGeneral can't do this, as it doesn't even pass blank lines and comments between commands to the Narya subprocess.  However, most people already separate their commands by single blank lines, so this difference is not usually a serious issue.  If a file has been formatted by the command-line reformatter, processing it in Proof General should not *change* that formatting (if it does, please report a bug).

It is not currently possible to reformat code without simultaneously typechecking it.  The presence of user-definable mixfix notations that can also be imported from other files means that any reformatter must be at least partially context-aware.  It would probably be possible to implement a reformatter that resolves user-defined notations without typechecking definitions, but this is not a high priority.

Currently there is only one configuration option for the code formatter: whether to print Unicode characters such as → or their ASCII equivalents such as ``->``.  This can be set on the command line with the flags ``-unicode`` and ``-ascii``, and in ProofGeneral with the state-preserving ``display`` command.  In accord with the goal of opinionated code formatters -- to eliminate time wasted by arguing about formatting, including formatter options -- I do not plan to add more configuration options; although I'll listen if you have a case to make for one.  Suggestions for improvements and changes to the standard formatting style are also welcome, although I can't promise to adopt them.

It is possible to turn off the code formatter.  The Emacs customization variables ``narya-reformat-commands`` and ``narya-reformat-holes`` will turn off reformatting in ProofGeneral, and the command-line option ``-no-format`` will turn off reformatting of input files.  However, if you don't like the way Narya reformats your code, I would appreciate it if you give me feedback about this rather than (or, at least, in addition to) turning it off entirely.

jsNarya
-------

jsNarya is a JavaScript version of Narya that runs in a browser.  Its functionality is limited to the equivalent of ``narya -e "STARTUP" -i``: you can specify a single startup "file" by copying and pasting it into a text box, and then you drop into interactive mode.  Also there is no real Unicode input-mode, although there is a palette of buttons that can be used to enter a number of common Unicode characters.  These limitations are not intrinsic; we just have not yet found or implemented an appropriate frontend for anything more complicated.

jsNarya does accept customization of the arity, direction name, and internality of parametricity, plus discreteness, for :ref:`Observational higher dimensions`.  This can be done with input elements on the page before starting the interactive mode, or with appropriately-named URL parameters.  For instance, supplying the URL query string ``?arity=1&direction=d&external`` yields :ref:`Poor man's dTT<Internal versus external parametricity>`, and this special case admits the shortcut ``?dtt``.  The startup code can also be specified in the URL with the ``?startup=`` parameter.

