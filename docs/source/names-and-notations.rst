Names and notations
===================

Mixfix notations
----------------

When a constant is declared with the ``def`` command, it is always a function that must be applied to all its arguments in the usual way.  For instance, if we define ``ℕ.plus : ℕ → ℕ → ℕ``, then to add two natural numbers we must write ``ℕ.plus 3 5``.  Of course we would prefer to write ``3 + 5``; we can make this possible by associating a *notation* to the constant ``ℕ.plus``.  (Narya's behavior here is like that of Rocq and Lean: we must *first* define a constant, giving it an ordinary name, and *then* additionally associate it to a notation, in contrast to Agda where the notation for a constant *is* its name.)  For instance, here is a command that associates the "infix" notation ``+`` to ``ℕ.plus``:

.. code-block:: none

   notation(1) … m "+" n ≔ ℕ.plus m n

The two central parts of a ``notation`` command are the *pattern*, which in this case is ``m "+" n``, and the *meaning*, which in this case is ``ℕ.plus m n``.  The pattern, on the left-hand side of the ``≔``, describes what the notation looks like when you use it.  It consists of a sequence of interspersed *variables* (here ``m`` and ``n``) and double-quoted *symbols* (here ``"+"``).  When the notation is used, the variables are substituted by arbitrary terms, whereas the symbols appear verbatim (without the double quotes).

The meaning, on the right-hand side of the ``≔``, tells Narya how to interpret the notation when it is used.  In this case, we say that the two terms replacing ``m`` and ``n`` in the notation should be supplied as arguments to the constant ``ℕ.plus``.  Thus, for instance, ``3 + 5`` is interpreted as ``ℕ.plus 3 5``, as we intended.

In general, the pattern can be any sequence of distinct variables and double-quoted symbols.  It can start with either a variable or a symbol, and end with either a variable or a symbol; two or more symbols can appear next to each other, but two variables cannot appear next to each other with no symbols in between; and there must be at least one symbol.

- A pattern like the above ``m "+" n`` that both starts and ends with variables is called *infix*.
- A pattern that starts with a symbol and ends with a variable is called *prefix*, such as unary arithmetic negation ``"-" x`` or logical negation ``"¬" x``.
- A pattern that starts with a variable and ends with a symbol is called *postfix*, such as factorial ``n "!"``.
- A pattern that both starts and ends with symbols is called *outfix* (or sometimes "closed"), such as the absolute value ``"|" x "|"``.

The general class of notations that includes infix, prefix, postfix, and outfix notations is known as *mixfix*.  Some examples of notations with more than one symbol are the relation of modular congruence, ``a "≡" b "mod" n``, the typing relation ``Γ "⊢" x "⦂" A``, and the if-then-else test operation on booleans, ``"if" a "then" b "else" c``.  (We cannot use the C-style ``a "?" b ":" c`` since both ``?`` and ``:`` have special meaning to Narya.)  These examples make clear that "symbols" do not have to be symbols in the colloqiual sense, but can also be words; in general a symbol can be any *token* (see :ref:`Tokens`).

The number ``(1)`` in parentheses after the ``notation`` keyword is the *tightness* of the notation.  This governs how it interacts with other notations.  For instance, if ``m "+" n`` is associated to ``ℕ.plus`` and ``m "*" n`` is associated to ``ℕ.times``, then how should we interpret ``m + n * p``?  We are used to the fact that multiplication *binds more tightly* than addition and so this should mean ``m + (n * p)``: this is specified by giving multiplication a higher tightness than addition.  Often tightness is known as *precedence*, but we prefer the word "tightness" to emphasize that higher numbers bind more tightly.

Infix, prefix, and postfix notations *must* have a tightness, while outfix notations must *not* have one.  A tightness must be a *dyadic rational number* (i.e. having denominator a power of 2), written in decimal notation, such as 0, 1, 2, -1, 1.5, 0.75, -0.375, etc.  Tightnesses +ω and −ω also exist, but are reserved for internal use.  The tightness is relevant only on the side(s) where a notation is "open" (both sides for an infix notation, the right for a prefix one, and the left for a postfix one).

Finally, the ellipsis ``…`` at the beginning of the example pattern above indicates that the notation is *left associative*.  This governs how it interacts with other notations having the same tightness (such as, in particular, itself).  For instance, since we declared addition to be left-associative, ``m + n + p`` will be interpreted as ``(m + n) + p``.  If we had declared it to be right-associative instead, with a ``…`` at the *end* of the pattern, then ``m + n + p`` would be interpreted as ``m + (n + p)``.  Of course in the case of addition the two are provably (though not definitionally) equal, but this is not the case for, say, subtraction, which is conventionally left-associative.  An infix notation can be either left- or right-associative or neither, but not both.  A prefix notation can be right-associative or neither, a postfix notation can be left-associative or neither, while an outfix notation cannot be associative.

The general form of the ``notation`` command is therefore:

.. code-block:: none

   notation [(TIGHTNESS)] […] PATTERN […] ≔ HEAD ARGUMENTS

We require the meaning (on the right side of the ``≔``) to have a special form: it must be a *head*, which is either a defined constant or a datatype constructor (see :ref:`Inductive datatypes and matching`), followed by a list of *exactly the same variables* that appear in the pattern, though perhaps in a different order.  This requirement enables Narya to *print* applications of the head by using the notation, in addition to *parsing* uses of the notation as applications of the head.  A constant can be associated to only one notation for printing it; if additional notations are declared later, they will all remain usable for parsing, but it is unpredictable which of them will be used for printing.  A constructor can be associated to one printing notation for each number of arguments it could be applied to, since the same constructor name could be used at different datatypes with different numbers of arguments.

Every notation is automatically also assigned a *name*, which is obtained from its pattern by replacing the variables with ``_``, concatenating them and the symbols (unquoted) separated by spaces, and surrounding it with guillemets ``«»`` so that it becomes an atomic identifier.  The notation is then associated to this name in the namespace ``notations`` (see :ref:`Importing notations`).

The right-associative function-type notation ``A → B`` is built-in with tightness 0.  Function abstraction ``x ↦ M`` is also right-associative, so you can write ``x ↦ y ↦ M`` (which can also be abbreviated as ``x y ↦ M``), and has tightness −ω.  Application ``M N`` is implemented specially since an ordinary notation cannot have two variables next to each other without a symbol in between, but it behaves as though it is left-associative with tightness +ω.  (In particular, a nonassociative prefix notation of tightness +ω, say ``@``, will bind tighter than application, so that ``@ f x`` parses as ``(@ f) x``.  However, there are no such notations yet.)

Parentheses ``( M )`` are defined as an outfix notation, hence with effective tightness +ω.  This emphasizes that the "internal" locations of any notation (those with notation symbols on both sides) behave as if surrounded by parentheses; in particular, notations of any tightness, even −ω, can appear therein without further parenthesization.  Tightness and associativity only control what other notations can appear in the "external" locations that are delimited by a notation symbol on one side only.

In general, ambiguities in parsing are treated as errors.  However, *potential* ambiguities are *not* reported at the time when notations are declared, since this can easily happen accidentally when importing notations from multiple libraries, and causes no problems as long as no ambiguities are actually encountered in parsing.  But an error is reported whenever an ambiguity is encountered during parsing.  In addition, some notation combinations that are not technically ambiguous are not allowed because parsing them correctly would require too much backtracking.  Specifically, the sequence of "inner" operators and variables (that is, the pattern except for any initial variable and ending variable) of one notation is not allowed to be a *prefix* of that of any other notation (including the case when the two are the same).  Thus, for instance, a notation such as ``if CONDITION then EXPR`` cannot coexist with one such as ``if CONDITION then EXPR else EXPR`` (where ``if``, ``then``, and ``else`` are notation symbols): even though *some* uses of these two notations would be unambiguous, if both are declared then an error will be reported as soon as either one is used.

There is one exception to this: if more than one declared notation has exactly the same sequence of "inner" operators and variables, but exactly one of those notations is left-open (infix or postfix), then ambiguities in parsing are resolved in favor of the left-open notation.  This is the only possible resolution if ambiguities are to be accepted in this situation, since if a left-closed notation is intended, it can be disambiguated with parentheses, whereas the left-open case cannot.  The primary example of this situation is the combination of infix binary subtraction ``a - b`` with prefix unary minus ``- a`` using the same symbol ``-``, where the interpretation of ``a - b`` as the function ``a`` applied to ``- b`` can be disambiguated by writing ``a (- b)``.  (In principle, it would be possible to also allow the dual situation of exactly one *right*-open notation, but this would be more difficult to parse without backtracking, and I don't know of any important applications for it.)

Comments and strings
--------------------

There are two kinds of comments.  A line comment starts with a backquote ````` and extends to the end of the line.  A block comment starts with ``{``` and ends with ```}``.  Block comments can be nested and can contain line comments, but cannot start inside a line comment.

String literals are surrounded by double quotes, as in ``"hello, world"``.  Currently, double-quoted strings appear in the syntax of some commands, such as ``notation`` and ``import``, but do not exist internally in the language of Narya.


Tokens
------

A Narya source file is expected to be UTF-8 encoded and can contain arbitrary Unicode.  As usual, the code is first *lexed* by separating it into "tokens", and then the sequence of tokens is *parsed* into an abstract syntax tree of notations.  Both identifiers (variable and constant names) and the symbols in a mixfix notation are tokens.  Whitespace (including comments) always creates a token boundary.  And since notation symbols can be made of the same characters that might be in an identifier, whitespace is sometimes necessary to separate identifiers from symbols.  For instance, if ``⋆`` is defined as a binary operator, we cannot write ``x⋆y`` (or even ``1⋆1``) since that would be lexed as a single token.

However, there are the following exceptions to this, where whitespace is not needed to separate tokens:

- The characters ``( ) [ ] { } → ↦ ⤇ ≔ ⩴ ⩲ … ? ! ⁇ ¿ ʔ``, which either have built-in meaning or are reserved for future built-in meanings, are always treated as single tokens.  Thus, they do not need to be surrounded by whitespace.  This is the case for parentheses and braces in most languages, but in Narya you can also write, e.g., ``A→B`` without spaces.  Many of the non-ASCII characters in this group have ASCII-sequence substitutes that are completely interchangeable: ``-> |-> |=> := ::= += ...``.  Additional characters may be added to this list in the future.

- A nonempty string consisting of the characters ``~ @ # $ % & * / = + | , < > : ; - ^`` is always treated as a single token, and does not need to be surrounded by whitespace.  Moreover, such tokens may only be notation symbols, not identifiers.  Note that this is most of the non-alphanumeric characters that appear on a standard US keyboard except for those that already have another meaning (parentheses, backquote, double quote, curly braces) or are allowed in identifiers (period, underscore, and single quote).  In particular:

   - Ordinary algebraic operations like ``+`` and ``*`` can be defined so that ``x+y`` and ``x*y`` are valid.
   
   - This includes the colon, so you can write ``(x:A) → B``, and similarly for the comma ``,`` in a tuple and the bar ``|`` in a :ref:`match<Matching>` or :ref:`comatch<Copattern matching>`.  But the user can also use these characters in other operators.
   
   - The ASCII substitutes for most of the single-token Unicode characters also fall into this category, so you can write for instance ``A->B``.
   
   - The ASCII hyphen ``-`` is in this category; in addition to its being part of ``->`` and ``|->``, this allows a subtraction operator ``x-y`` to be written without spaces. Therefore, unlike in Agda, the hyphen is not allowed in identifiers.
   
   - The backslash ``\`` is *not* in this category.  This is chosen with a view towards supporting TeX notations, so that commands like ``\alpha`` can be treated as a single token.

  This rule is intended to be a compromise, allowing the user to define plenty of infix operators that don't require spacing but also arbitrary unicode operators, while keeping the lexer rules simple and unchanging as new operators are defined.  However, feedback is welcome!

- A nonempty string such as ``⁽¹ᵉ³⁾`` consisting of Unicode superscript letter, digit, and hyphen characters, ``ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖʳˢᵗᵘᵛʷˣʸᶻ⁰¹²³⁴⁵⁶⁷⁸⁹⁻``, in between Unicode superscript parentheses, ``⁽`` and ``⁾``, is treated as a single token and applied as a "superscript" operator to whatever immediately precedes it.  This is used for generic degeneracies in :ref:`Observational higher dimensions`.  It binds more tightly than anything (tightness of "ω+1"), including function application, so that ``f⁽ᵉ⁾ x`` means ``(f⁽ᵉ⁾) x`` and ``f x⁽ᵉ⁾`` means ``f (x⁽ᵉ⁾)``.  In addition, a double caret ``^^`` followed by a nonempty string of the corresponding ASCII characters ``abcdefghijklmnopqrstuvwxyz0123456789-`` (no internal spaces!) in between ordinary parentheses ``(`` and ``)`` has exactly the same meaning with the same tightness: ``f^^(e) x`` means the same as ``f⁽ᵉ⁾ x``.  (Unicode subscript characters are not treated specially; thus they may appear freely in identifiers or symbols, as may unicode superscripts not involving any parentheses.  Single carets can be used as ordinary ASCII operators.)

Identifiers
-----------

An *atomic identifier* can be any string of non-whitespace characters, other than those mentioned above as special, not containing any periods, not starting with an underscore, does not consist entirely of digits, and is not a reserved word.  Currently the reserved words are

.. code-block:: none
   
   and axiom codata data def display echo end export import chdir in let match
   notation option quit rec return section show sig solve synth undo

An *identifier* consists of one or more atomic identifiers joined by periods.  Variable names must be atomic identifiers, while constant names must be identifiers (internal periods denote :ref:`namespaces<Namespaces and sections>`).  In particular, (atomic) identifiers may *start* with a digit, such as for instance ``2Cat`` or ``2−Cat`` for the type of 2-categories.

In addition, enclosing guillemets ``«`` and ``»`` can be used to make an atomic identifier out of *any* sequence of characters at all, including spaces, periods, comment sequences, and special characters.  Thus, for instance, ``«a long string»`` is a single atomic identifier, and likewise ``«foo.bar»`` is a single *atomic* identifier (unlike ``foo.bar`` which is ``bar`` in namespace ``foo``).  Note that the guillemets in such cases are *part* of the identifier: thus for instance ``«foo»`` is a different identifier than ``foo``.  Guillemets can also be nested: ``«a«b»c»`` is a single atomic identifier.

Default names
-------------

Sometimes, when printing terms, Narya needs to generate a name for variables that the user has left unnamed.  For instance, this happens when displaying the context of a :ref:`hole<Holes>` inside an unnamed abstraction such as ``_ ↦ ?``.  It also happens when printing the :ref:`higher-dimensional version<Id of function types>` of a non-dependent function type such as ``Id (A → B) f g``.

To deal with cases like this, Narya maintains a list of "default variable names", and whenever it needs such a name it looks through that list until it finds one that hasn't been used in the current context.  If all of them have been used, it goes back to the beginning and tries them all with a single prime ``′``, and so on through ``″``, ``‴``, and so on.  The default list of default variable names is

.. code-block:: none

   𝑥 𝑦 𝑧 𝑤 𝑢 𝑣

Here ``𝑥`` is the unicode character MATHEMATICAL ITALIC SMALL X, and so on.  These are chosen because *x*, *y*, and so on are common "neutral" variable names in mathematics, while their unicode italic versions are not commonly used in coding.  However, you can change the default variable names with the command-line flag ``-variables``, which takes a comma-separated list of variable names, such as ``-variables 𝑎,𝑏,𝑐`` if you prefer the beginning of the alphabet, or ``-variables 𝓍,𝓎,𝓏`` if you prefer a different font.
