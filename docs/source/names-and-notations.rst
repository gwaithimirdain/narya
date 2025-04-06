Names and notations
===================

Mixfix notations
----------------

The parser supports arbitrary mixfix operations with associativities and precedences, although we prefer to say "tightness" instead of "precedence", to make it clear that higher numbers bind more tightly.  Tightnesses are *dyadic rational numbers* (i.e. having denominator a power of 2), written in decimal notation.  Tightnesses +ω and −ω also exist, but are reserved for internal use.  Some notations are built in, but the user can also declare new notations with the ``notation`` command mentioned above.

The ``PATTERN`` of a notation is a list of interspersed distinct local variable names and double-quoted symbols, such as ``x "+" y`` for addition or ``Γ "⊢" x "⦂" A`` for a typing judgment.  Each quoted symbol must be exactly one token (see below); any two variables must be separated by a symbol (but two symbols can follow each other without a variable in between); and there must be at least one symbol.  If the pattern starts with a variable, it may be preceded by an ellipsis ``…``, indicating that it is left-associative; and dually if it ends with a variable, it may be followed by an ellipsis, indicating that it is right-associative (but not both).

A notation which starts and ends with a variable is called "infix"; one that starts with a symbol and ends with a variable is called "prefix"; one that starts with a variable and ends with a symbol is called "postfix"; and one that starts and ends with a symbol is called "outfix".  An outfix notation *may not* have a tightness (it always behaves as if it has tightness +ω).  All other notations must have a tightness, which is relevant only on the side(s) where they are "open" (both sides for an infix notation, the right for a prefix one, and the left for a postfix one).

As noted above, the meaning of a notation is defined by a ``HEAD``, which is either a defined constant or a datatype constructor (see below), and ``ARGUMENTS`` that are a permutation of the pattern variables.  When the notation is encountered during parsing, it will be interpreted as a corresponding application of this head to the appropriate permutation of the terms appearing in the notation.  Conversely, this notation is also associated to the constant or constructor and will also be used for *printing* it in output.  A constant can be associated to only one notation for printing it; if additional notations are declared later, they will all remain usable for parsing, but only the most recently declared one will be used for printing.  A constructor can be associated to one printing notation for each number of arguments it could be applied to, since the same constructor name could be used at different datatypes with different numbers of arguments (see below).

We have already mentioned the right-associative function-type notation ``A → B``; this has tightness 0.  Function abstraction ``x ↦ M`` is also right-associative, so you can write ``x ↦ y ↦ M`` (which can also be abbreviated as ``x y ↦ M``), and has tightness −ω.  Application ``M N`` is implemented specially since an ordinary notation cannot have two variables next to each other without a symbol in between, but it behaves as though it is left-associative with tightness +ω.  (In particular, a nonassociative prefix notation of tightness +ω, say ``@``, will bind tighter than application, so that ``@ f x`` parses as ``(@ f) x``.  However, there are no such notations yet.)

In addition, parentheses ``( M )`` are defined as an outfix notation, hence with effective tightness +ω.  This emphasizes that the "internal" locations of any notation (those with notation symbols on both sides) behave as if surrounded by parentheses; in particular, notations of any tightness, even −ω, can appear therein without further parenthesization.  Tightness and associativity only control what other notations can appear in the "external" locations that are delimited by a notation symbol on one side only.


Comments and strings
--------------------

There are two kinds of comments.  A line comment starts with a backquote ````` and extends to the end of the line.  A block comment starts with ``{``` and ends with ```}``.  Block comments can be nested and can contain line comments, but cannot start inside a line comment.

String literals are surrounded by double-quotes, as in ``"hello, world"``.  At present the only use of string literals is in the ``notation`` command for defining user notations.


Tokens
------

A Narya source file is expected to be UTF-8 encoded and can contain arbitrary Unicode.  As usual, the code is first *lexed* by separating it into "tokens", and then the sequence of tokens is *parsed* into an abstract syntax tree of notations.  Both identifiers (variable and constant names) and the symbols in a mixfix notation are tokens.  Whitespace (including comments) always creates a token boundary.  And since notation symbols can be made of the same characters that might be in an identifier, whitespace is sometimes necessary to separate identifiers from symbols.  For instance, if ``⋆`` is defined as a binary operator, we cannot write ``x⋆y`` (or even ``1⋆1``) since that would be lexed as a single token.

However, in Narya there are the following exceptions to this, where whitespace is not needed to separate tokens:

- The characters ``( ) [ ] { } ? → ↦ ⤇ ≔ ⩴ ⩲ …``, which either have built-in meaning or are reserved for future built-in meanings, are always treated as single tokens.  Thus, they do not need to be surrounded by whitespace.  This is the case for parentheses and braces in most languages, but in Narya you can also write, e.g., ``A→B`` without spaces.  The non-ASCII characters in this group all have ASCII-sequence substitutes that are completely interchangeable: ``-> |-> |=> := ::= += ...``.  Additional characters may be added to this list in the future.
- A nonempty string consisting of the characters ``~ ! @ # $ % & * / = + \ | , < > : ; -`` is always treated as a single token, and does not need to be surrounded by whitespace.  Moreover, such tokens may only be notation symbols, not identifiers.  Note that this is most of the non-alphanumeric characters that appear on a standard US keyboard except for those that already have another meaning (parentheses, backquote, double quote, curly braces) or are allowed in identifiers (period, underscore, and single quote).  In particular:
  - Ordinary algebraic operations like ``+`` and ``*`` can be defined so that ``x+y`` and ``x*y`` are valid.
  - This includes the colon, so you can write ``(x:A) → B``, and similarly for the comma ``,`` in a tuple and the bar ``|`` in a match or comatch (see below).  But the user can also use these characters in other operators.
  - The ASCII substitutes for the single-token Unicode characters also fall into this category, so you can write for instance ``A->B``.
  - The ASCII hyphen ``-`` is in this category; in addition to its being part of ``->`` and ``|->``, this allows a subtraction operator ``x-y`` to be written without spaces.  (Note, though, that the current parser does not permit a binary subtraction to coexist with a unary negation using the same character.)  Therefore, unlike in Agda, the hyphen is not allowed in identifiers.

  This rule is intended to be a compromise, allowing the user to define plenty of infix operators that don't require spacing but also arbitrary unicode operators, while keeping the lexer rules simple and unchanging as new operators are defined.  However, feedback is welcome!

- A nonempty string such as ``⁽¹ᵉ³⁾`` consisting of Unicode superscript letter, digit, and hyphen characters, ``ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖʳˢᵗᵘᵛʷˣʸᶻ⁰¹²³⁴⁵⁶⁷⁸⁹⁻``, in between Unicode superscript parentheses, ``⁽`` and ``⁾``, is treated as a single token and applied as a "superscript" operator to whatever immediately precedes it.  This is used for generic degeneracies (see below).  It binds more tightly than anything (tightness of "ω+1"), including function application, so that ``f⁽ᵉ⁾ x`` means ``(f⁽ᵉ⁾) x`` and ``f x⁽ᵉ⁾`` means ``f (x⁽ᵉ⁾)``.  In addition, a caret ``^`` followed by a nonempty string of the corresponding ASCII characters ``abcdefghijklmnopqrstuvwxyz0123456789-`` (no internal spaces!) in between ordinary parentheses ``(`` and ``)`` has exactly the same meaning with the same tightness: ``f^(e) x`` means the same as ``f⁽ᵉ⁾ x``.  (Unicode subscript characters are not treated specially; thus they may appear freely in identifiers or symbols, as may unicode superscripts not involving any parentheses.)


Identifiers
-----------

Identifiers (variables and constant names) can be any string of non-whitespace characters, other than those mentioned above as special, that does not start or end with a period or an underscore, and is not a reserved word.  Currently the reserved words are

.. code-block:: none
   
   let rec in def and axiom echo notation import export solve show quit undo match return sig data codata

In particular, identifiers may start with a digit, or even consist entirely of digits (thereby shadowing a numeral notation, see below).  Internal periods in identifiers denote namespace qualifiers on constants; thus they cannot appear in local variable names.

