Error codes
===========

This page lists the error codes that Narya can report. Click on a code to see
an explanation of it and, for most codes, a minimal example that triggers it.

The examples can be reproduced from the command line with ``narya -e '...'``.
Use single quotes around the code: many examples contain double quotes, as in
``notation(0) "~" x ≔ f x``, and inside a double-quoted argument the shell
would remove them, so that Narya reports a different error (usually ``E0200``).
Alternatively, save the example in a ``.ny`` file and run ``narya file.ny``.

Errors are grouped by the first two digits of their code.

Only codes that begin with ``E`` are listed here. Narya also reports warnings,
hints and informational messages whose codes begin with ``W``, ``H`` and
``I``, such as ``W0210`` or ``H0403``; these do not have entries on this page.
A few ``E`` codes are warnings or hints despite their letter, which is noted
in their entries. Conversely, ``I3005`` (an invalid ``split``) is reported as
an error despite its letter.

.. raw:: html

   <style>
     details.error-code { margin: 0.4em 0; border: 1px solid #e1e4e5; border-radius: 4px; }
     details.error-code > summary { cursor: pointer; padding: 0.5em 0.8em; font-weight: bold; background: #f3f6f6; }
     details.error-code > summary code { font-weight: bold; }
     details.error-code[open] > summary { border-bottom: 1px solid #e1e4e5; }
     details.error-code > :not(summary) { margin-left: 0.8em; margin-right: 0.8em; }
     details.error-code > p:first-of-type { margin-top: 0.6em; }
     details.error-code p { margin-bottom: 0.6em; line-height: 1.4; }
     details.error-code div[class^="highlight"] { margin: 0.4em 0 0.6em 0; border: 1px solid #ece6d3; border-radius: 3px; }
     details.error-code div[class^="highlight"] pre { padding: 0.5em 0.8em; line-height: 1.3; background: #fdf9ee; }
     details.error-code p strong { display: block; margin-top: 0.8em; }
     details.error-code div.admonition { margin: 0.6em 0; }
     h2.error-group { font-size: 1.3em; margin: 1.4em 0 0.5em 0; }
     ul.error-pending { margin-top: 0.4em; }
   </style>

.. raw:: html

   <h2 class="error-group">E00xx: Internal errors</h2>

.. raw:: html

   <details class="error-code" id="E0000"><summary><code>E0000</code> Anomaly</summary>

This is the generic error of this group: Narya has reached a state that its own
code considers impossible. The message says which invariant was violated. This
is not a user error but a bug in Narya, and it should be reported to the
developers together with the code that triggered it.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0001"><summary><code>E0001</code> No_such_level</summary>

This error is reported when, during readback, a level variable is not found in
the current context. In values, Narya represents free variables by de Bruijn
levels, and readback looks each of them up in the current context; this error
means that the value depends on a variable that does not exist in the context
in which it is being read back. Narya normally catches this error and turns it
into a more specific one. Seeing it indicates a bug in Narya, which should be
reported to the developers.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0002"><summary><code>E0002</code> Dependent</summary>

This is a silent error. It indicates that the input depends on a part that has
already failed. Since the real error has already been reported, it is never
shown to the user; it only stops the work on the part that depends on the
failed one.

In Narya, mortal errors do not stop checking: Narya reports the error, marks
that part as failed, and continues, so that more than one error can be shown.
But when whatever was put in place of the failed part is used, the
``Dependent`` error arises.

If a command fails with only silent errors, this is an internal inconsistency,
and in interactive modes it is converted into an ``E0000`` error.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0003"><summary><code>E0003</code> Invalid_degeneracy_action</summary>

This error is reported when a degeneracy is applied internally to an object
whose dimension does not factor through the codomain of that degeneracy. The
message has the form ``invalid degeneracy action on …: dimension '…' doesn't
factor through codomain '…'``, and gives the kind of the object, its
dimension, and the codomain of the degeneracy.

Degeneracies written by the user are checked in the typechecker before they
reach this point: if the dimension of the argument or of its type is too low,
``E0601`` or ``E0602`` is reported, and an unrecognized degeneracy name gives
``E0206``. Therefore, ``E0003`` means that the dimensions do not match while acting on a value that
has already passed checking. Seeing it indicates a bug in Narya, which should
be reported to the developers.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0004"><summary><code>E0004</code> Self_used</summary>

The printer uses this error as a signal while printing a record type: it first
tries to display the fields as named variables, raises this error if the
self-variable is used other than through a field projection, and then falls
back to self-variable syntax. The message is ``uncaught use of self-variable
in a field-variable record display``. The error is always caught by the
printer. Seeing it indicates a bug in Narya, which should be reported to the
developers.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0005"><summary><code>E0005</code> Evaluating_display_term</summary>

This error is reported when the evaluator is asked to evaluate a term that
exists only for display purposes (for instance a printed piece of a case tree
or of a codata type). Such terms are never supposed to be evaluated. Seeing
this error indicates a bug in Narya, which should be reported to the
developers.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0006"><summary><code>E0006</code> Fatalize</summary>

This is a silent error. It ends a region of checking in which one or more
mortal errors have already been reported. A mortal error is shown to the user
but lets checking continue, so that other errors in the same term can also be
found; at the end of such a region, the accumulated errors must be turned into
a real failure, since otherwise an erroneous definition would be accepted.
``Fatalize`` is the error that does this. It is never shown to the user.

It differs from ``E0002``, which says that something depends on a part that
has already failed: if all of the accumulated errors are ``E0002``, then
``E0002`` is raised instead of ``E0006``, so that the dependency information
is passed on. If a command fails with only silent errors, in interactive modes
it is converted into an ``E0000`` error.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0007"><summary><code>E0007</code> Typeless_meta</summary>

This error is reported when a metavariable created internally by Narya is
referred to before it has been given a type. The message has the form
``typeless meta in let-binding: …`` or ``typeless meta in bare case tree: …``.

Case tree constructs such as ``match``, ``comatch`` and canonical type
declarations can only appear at the top level of a definition. To allow them
elsewhere, Narya creates a metavariable behind the scenes in two situations:
for a ``let`` binding whose value contains a case tree construct, and for a
bare ``match`` written in a synthesizing position inside an ordinary term
(where the hint ``H0403`` is also given). If the value has no explicit type,
the type of the metavariable is only synthesized while its body is being
checked; until then, asking for the type or the definition of the metavariable
raises this error.

This should not happen on normal input: in the ``let`` case the variable is
not in scope while its value is being checked, and in the bare ``match`` case
the metavariable does not even have a name. Seeing this error means that the typeless metavariable has leaked out in some
unexpected way; it indicates a bug in Narya, which should be reported to the
developers.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E01xx: Unimplemented or deprecated features</h2>

.. raw:: html

   <details class="error-code" id="E0100"><summary><code>E0100</code> Unimplemented</summary>

This error is reported when the input uses a feature that Narya recognizes but
does not implement yet. The message names the feature, for example unification
arguments (a bare ``_`` used as a term), general implicit function types, or
higher constructors. If the syntax is not recognized at all, ``E0200`` is
reported instead; for features that still work but are deprecated, the warning
``E0101`` is used.

**Example**

.. code-block:: none

   echo _

   ￫ error[E0100]
   ￭ command-line exec string
   1 | echo _
     ^ unimplemented: unification arguments

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0101"><summary><code>E0101</code> Deprecated</summary>

This warning is reported when the input uses a syntax or a command-line flag
that still works but is deprecated and may be removed in the future. This is a
warning: it is printed as ``warning[E0101]`` and does not stop processing, and
the input continues to be processed with its old meaning. The message has the
form ``deprecated: …``.

Being a warning, it does not make a command fail by itself; but if the old
syntax also leads to another error (``E1504``, for instance), the output shows
this warning first and then that error. It differs from ``E0100`` in that
there the feature does not work at all, while here it works but is not
recommended.

**Example**

With the ``-parametric`` flag, the definition of ``Gel`` below is accepted;
only the ``a b ↦`` part is reported as old syntax.

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ ( ungel : R a b )

   ￫ warning[E0101]
   ￭ command-line exec string
   1 | def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b ↦ ( ungel : R a b )
     ^ deprecated: 'sig … ↦' for higher records: use self variables

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E02xx: Parse errors</h2>

.. raw:: html

   <details class="error-code" id="E0200"><summary><code>E0200</code> Parse_error</summary>

This error is reported when the input is not valid Narya syntax. Typical
reasons are unbalanced parentheses, a missing ``≔``, an operator that is not a
defined notation, or a field projection with nothing in front of it. The
reported location is the first token that the parser cannot interpret. In the
case of an extra or misplaced token, this is the error itself; in the case of
a missing element (such as an unclosed parenthesis), it is the token
immediately following the incomplete expression, which may appear on a
subsequent line.

**Examples**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom x : A
   echo f (x

   ￫ error[E0200]
   ￭ command-line exec string
   4 | echo f (x‹EOF›
     ^ parse error: invalid syntax

If the input ends with a newline, as a file normally does, the end of input is
reported on the next line instead, as ``5 | ‹EOF›``.

Here ``echo f (x)`` is executed first, and only the extra ``)`` is rejected:

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom x : A
   echo f (x) )

   f x
     : A

   ￫ error[E0200]
   ￭ command-line exec string
   4 | echo f (x) )
     ^ parse error: invalid syntax

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0201"><summary><code>E0201</code> Parsing_ambiguity</summary>

This error is reported when two notations that are currently in scope could
both apply to the same input, because one of them is a prefix of the other.
The parser refuses to guess which one was meant. This is reported only when
such an input is actually parsed, not when the notations are defined, and the
error carries no source location.

The most common cause is defining exactly the same notation twice, which also
produces the warnings ``E2100`` and ``E2209`` at the point of the second
definition.

**Examples**

Two distinct notations, one a prefix of the other:

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom g : A → A → A
   notation(0) "~" x ≔ f x
   notation(0) "~" x "~" y ≔ g x y
   axiom a : A
   echo ~ a

   ￫ error[E0201]
   ￮ potential ambiguity (one notation is a prefix of another). Notations involved:
       «~ _»
       «~ _ ~ _»

The same notation defined twice:

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   notation(0) "-" x ≔ f x
   notation(0) "-" x ≔ f x
   axiom a : A
   echo - a

   ￫ warning[E2100]
   ￭ command-line exec string
   3 | notation(0) "-" x ≔ f x
     ^ previous definition
   4 | notation(0) "-" x ≔ f x
     ^ redefining constant: notations.«- _»

   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)

   ￫ error[E0201]
   ￮ potential ambiguity (one notation is a prefix of another). Notations involved:
       «- _»
       «- _»

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0202"><summary><code>E0202</code> Invalid_variable</summary>

This error is reported when a local variable name (bound by ``let``, ``↦``, a
``match`` pattern, the ``variables`` attribute, or a ``notation`` pattern) is
not a valid identifier. Local names must not contain a period. The placeholder
``_`` is accepted in place of a variable bound by ``let``, ``↦`` or a
``match`` pattern, but not where a list of names is given: in a ``variables``
attribute and in the ``display variables`` command it gives this error. The
names passed to the ``-variables`` command-line flag are checked in the same
way; in that case the error has no source location.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A → A
   notation(0) x "&" y.z := f x y.z
   
   ￫ error[E0202]
   ￭ command-line exec string
   3 | notation(0) x "&" y.z := f x y.z
     ^ invalid local variable name: y.z

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0203"><summary><code>E0203</code> Invalid_field</summary>

This error is reported when a field projection such as ``x .fs.t`` is not a
valid field name. After the leading period, a field name may be followed only
by a single numeric suffix (as in ``.fst.1``), not by further alphabetic
components.

**Example**

.. code-block:: none

   echo (x |-> x .fs.t y)

   ￫ error[E0203]
   ￭ command-line exec string
   1 | echo (x |-> x .fs.t y)
     ^ invalid field name: .fs.t

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0204"><summary><code>E0204</code> Invalid_constr</summary>

This code is reserved for an invalid constructor name. The message has the
form ``invalid constructor name: …``. In the current source code this error is
not raised anywhere, so users are not expected to see it.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0205"><summary><code>E0205</code> Invalid_numeral</summary>

This error is reported when a token consisting of digits and periods is not a
well-formed numeral. Numerals may contain at most one period (as in a decimal
literal such as ``0.5``); something like ``0.1.2`` is rejected.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   echo (x |-> f 0.1.2 x)

   ￫ error[E0205]
   ￭ command-line exec string
   3 | echo (x |-> f 0.1.2 x)
     ^ invalid numeral: 0.1.2

   ￫ error[E0400]
   ￮ non-synthesizing term in synthesizing position (argument of echo)

The second error is unrelated to the numeral: it arises because an abstraction
given to ``echo`` cannot synthesize a type (see ``E0400``).

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0206"><summary><code>E0206</code> Invalid_degeneracy</summary>

This error is reported when a superscript such as ``A⁽ᵈ⁾`` (or, in ASCII,
``A^^(d)`` with a double caret) does not name a degeneracy that is valid for
the current settings. The available degeneracy names depend on the
``-direction`` flag, not on the arity: a superscript is built from the
direction letter, which is ``e`` by default, and digits, so ``d`` is
recognized only when the direction letter is changed, for instance with
``-dtt``. The names ``refl`` and ``Id`` are prefix operators, not
superscripts: ``A⁽ʳᵉᶠˡ⁾`` gives this error too.

Neighboring codes: if the degeneracy name is valid but the dimension of the
term it is applied to is too low, ``E0601`` is reported (for example
``A⁽¹ᵉ⁾`` for a zero-dimensional ``A``), and if the dimension of its type is
too low, ``E0602``; if a named degeneracy such as ``refl`` is used without an
argument, ``E0600``.
If the bytes of the superscript cannot be decoded as UTF-8, the error is in
theory ``E0212``; and a degeneracy applied internally at the wrong dimension is
the internal error ``E0003``.

**Example**

.. code-block:: none

   axiom A : Type
   echo A⁽ᵈ⁾

   ￫ error[E0206]
   ￭ command-line exec string
   2 | echo A⁽ᵈ⁾
     ^ invalid degeneracy: d

If the same example is run with the ``-dtt`` flag (``narya -dtt -e``), the
degeneracy ``d`` is recognized and the example is accepted without an error.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0207"><summary><code>E0207</code> No_relative_precedence</summary>

This error is reported when two notations are used next to each other without
parentheses, but their tightness and associativity do not determine how to
group them: for example two different infix notations of the same tightness,
or a non-associative infix notation chained with itself. Such notations can
only be combined using parentheses.

Neighboring codes: ``E0201`` arises when one of two notations is a prefix of
the other, that is, when it is ambiguous which one should be read; here both
notations are recognized without any problem, and what is ambiguous is how
they nest. If the notation is not defined at all, ``E0200`` is reported. This error is detected after the tokens have been read successfully, and its
location is the second notation, the one that would take the first as its
argument.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A → A
   notation(0) x "+" y ≔ f x y
   axiom a : A
   echo a + a + a

   ￫ error[E0207]
   ￭ command-line exec string
   5 | echo a + a + a
     ^ notations "«_ + _»" and "«_ + _»" have no relative precedence or associativity; they can only be combined with parentheses

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0208"><summary><code>E0208</code> Unrecognized_attribute</summary>

This error is reported when an attribute ``#(…)`` is not one that Narya knows
for the construct it is attached to, or it is missing its value. Attributes
can be written on a ``data``, ``sig`` or ``codata`` definition, on a ``match``
or a comatch, and after ``axiom``. Currently the recognized attributes are:

- ``#(variables ≔ …)`` or ``#(variables ⩲ …)``, with a comma-separated list of
  names, on any of ``data``, ``sig`` and ``codata``;
- ``#(opaque)``, ``#(transparent)`` and ``#(translucent)``, the last two
  optionally followed by ``labeled`` or ``positional``, on ``sig`` only (see
  :ref:`Eta-expansion and opacity`);
- ``#(nonparametric)`` on ``axiom`` only (see :ref:`Nonparametric axioms
  (deprecated)`);
- ``#(gen)`` on any of ``data``, ``sig``, ``codata``, ``match`` and a comatch.
  Narya writes this attribute itself when it prints a local case tree; parsing
  it back is accepted and gives only the warning ``W0210``. It is the only
  attribute that ``match`` and comatches accept.

**Examples**

A known attribute without its value:

.. code-block:: none

   def X : Type ≔ data #(variables) [ zero. ]

   ￫ error[E0208]
   ￭ command-line exec string
   1 | def X : Type ≔ data #(variables) [ zero. ]
     ^ unrecognized attribute

A record attribute applied to a datatype or a codatatype:

.. code-block:: none

   def X : Type ≔ data #(transparent) [ zero. ]

   ￫ error[E0208]
   ￭ command-line exec string
   1 | def X : Type ≔ data #(transparent) [ zero. ]
     ^ unrecognized attribute

.. code-block:: none

   def X : Type ≔ codata #(opaque) [ ]

   ￫ error[E0208]
   ￭ command-line exec string
   1 | def X : Type ≔ codata #(opaque) [ ]
     ^ unrecognized attribute

An unknown attribute on an ``axiom`` or on a ``match``:

.. code-block:: none

   axiom #(foo) B : Type

   ￫ error[E0208]
   ￭ command-line exec string
   1 | axiom #(foo) B : Type
     ^ unrecognized attribute

.. code-block:: none

   def N : Type ≔ data [ zero. ]
   def g (n : N) : N ≔ match #(foo) n [ zero. ↦ n ]

   ￫ error[E0208]
   ￭ command-line exec string
   2 | def g (n : N) : N ≔ match #(foo) n [ zero. ↦ n ]
     ^ unrecognized attribute

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0209"><summary><code>E0209</code> Display_only_syntax</summary>

This error is reported when the input contains syntax that Narya only produces
when printing and cannot parse back: the omission mark ``⋯`` (ASCII ``....``),
which stands for a part of a term left out of the display, or ``let only ⋯
in``. The message has the form ``display-only syntax can't be parsed: …`` and
says which syntax is involved. The typical cause is copying printed output and
pasting it back as input.

Rather than rejecting these marks with a generic ``E0200`` as unrecognized
syntax, Narya parses them deliberately, just so that it can give an
informative error.

**Example**

.. code-block:: none

   axiom A : Type
   echo ⋯ → A

   ￫ error[E0209]
   ￭ command-line exec string
   2 | echo ⋯ → A
     ^ display-only syntax can't be parsed: '⋯', which marks a part of a term omitted from display

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0211"><summary><code>E0211</code> Comment_end_in_string</summary>

This warning is reported when a quoted string contains the sequence ```}``,
which is also the block-comment terminator. If the surrounding code were later
commented out with ``{` … `}``, the comment would end inside the string. It is
reported as a warning and does not stop processing.

**Example**

.. code-block:: none

   chdir "a`}b"

   ￫ warning[E0211]
   ￮ comment-end sequence `} in quoted string: cannot be commented out

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0212"><summary><code>E0212</code> Encoding_error</summary>

This error is reported when a Unicode superscript (a degeneracy written in the
form ``⁽ᵉ⁾``) cannot be decoded as valid UTF-8. The message is ``UTF-8
encoding error``. Although its severity is an error, in practice it is a
safeguard: it does not appear to be reachable with ordinary input, including
input that contains invalid UTF-8 bytes.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E03xx: Scope errors</h2>

.. raw:: html

   <details class="error-code" id="E0300"><summary><code>E0300</code> Unbound_variable</summary>

This error is reported when a name written by the user cannot be resolved: it
is neither a local variable in scope nor a constant defined in scope. Typical
causes are a typo, a constant that has not yet been defined or imported, or a
variable whose scope has ended.

The error is not fatal: Narya reports it immediately, replaces the identifier
with a term that fails silently (``E0002``) when the typechecker reaches it,
and goes on to find errors in the other parts of the term that do not depend
on this name.

Neighboring codes: ``E0301``
indicates a constant that is found in scope but has no entry in the global
environment, which is a bug in Narya; ``E2208`` is for unbound variables in a
notation definition.

**Example**

.. code-block:: none

   echo g

   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo g
     ^ unbound variable: g

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0301"><summary><code>E0301</code> Undefined_constant</summary>

This is not a user error but a bug in Narya. Narya keeps two separate tables:
the scope, which maps names to constants, and the global environment, which
holds the type and definition of each constant. This error is raised when the
typechecker or the evaluator needs the definition of a constant that has no
entry at all in the global environment. An undefined name written by the user
is already rejected with ``E0300`` during name resolution, so this point is
reached only when the two tables have become inconsistent with each other.

A constant whose definition failed is not missing from the global environment:
it is kept there as a failed definition or as a recorded error, so using it
gives the silent ``E0002`` rather than this error. Similarly, a constant in a
mutual definition that has no declared type is recorded as an error until its
body has been checked, and using it before then gives ``E0402``. If the message ``undefined constant: …``
appears, there is nothing the user can fix; it should be reported to the
developers.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0302"><summary><code>E0302</code> Undefined_metavariable</summary>

This code is reserved for a metavariable (a hole left by the user, or an
unknown generated by Narya itself) that has no entry in the global
environment; it is the counterpart of ``E0301`` for metavariables. The message
has the form ``undefined metavariable: …``. In the current source code this
error is not raised anywhere, so users are not expected to see it.

The same situation is currently reported as a generic ``E0000`` with the same
message text. It means that a term is used after the state of the command it belongs to has
been undone, or in the wrong environment. Seeing it indicates a bug in Narya,
which should be reported to the developers. A metavariable whose
definition failed is, as for constants, recorded as an error, and that
recorded error is raised again. User errors such as referring to a hole number
that does not exist are unrelated; they are reported with their own codes.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0303"><summary><code>E0303</code> Locked_variable</summary>

This code is reserved for the use, inside an external degeneracy, of a local
variable that is not accessible there. The message is ``variable not available
inside external degeneracy``. With external parametricity (for example
``-dtt``), a degeneracy such as ``A⁽ᵈ⁾`` can only be applied to closed terms,
that is, terms that do not depend on ordinary variables in the context,
because no higher-dimensional counterpart of such a variable is available. The
argument of the degeneracy is therefore checked in a context in which those
variables are "locked".

In the current source code this error is not raised anywhere, so users are not
expected to see it. The restriction itself has not gone away: external
degeneracies are now handled by the modal machinery, so using a variable
behind such a lock is reported with a modal error from the ``E17xx`` family,
and variables removed from the context by a ``lock`` clause in ``let only`` or
by a key application are reported with ``E0306``. The counterpart of the
restriction for constants is still in use: a constant that relies on a
nonparametric axiom inside an external degeneracy gives ``E0304``.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0304"><summary><code>E0304</code> Locked_constant</summary>

This error is reported when a constant that is, or depends on, a
``#(nonparametric)`` axiom is used in a context that is under a modal lock.
The usual case is an external degeneracy such as ``A⁽ᵈ⁾``, which is what the
message mentions: nonparametric axioms have no higher-dimensional structure,
so this is not allowed. But the same error, with the same message, is reported
under any other nontrivial lock, for instance in the argument of ``♭.`` with
the ``-coreflector`` flag, where no degeneracy is involved. This error only
arises in modal type theories such as ``-dtt``. Nonparametric axioms are
deprecated; see :ref:`Nonparametric axioms (deprecated)`.

**Example**

Run this example with the ``-dtt`` flag. Without it, the degeneracy ``d`` is
not recognized and the error reported is ``E0206`` instead.

.. code-block:: none

   axiom #(nonparametric) A : Type
   echo A⁽ᵈ⁾

   ￫ error[E0304]
   ￭ command-line exec string
   2 | echo A⁽ᵈ⁾
     ^ constant A is or uses a nonparametric axiom, can't appear inside an external degeneracy

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0305"><summary><code>E0305</code> Axiom_in_parametric_definition</summary>

This error is reported when a command that is required to be parametric uses a
constant that is, or depends on, a ``#(nonparametric)`` axiom. Every constant
is either parametric (it can be used under external degeneracies) or not, and
a parametric constant cannot depend on something nonparametric, because then
its higher-dimensional counterpart could not be computed either. Unlike
``E0304``, this error is also reported with the default settings, not only
with external parametricity (for example ``-dtt``). Nonparametric axioms are
deprecated; see :ref:`Nonparametric axioms (deprecated)`.

**Example**

.. code-block:: none

   axiom #(nonparametric) A : Type
   axiom B : A → Type

   ￫ error[E0305]
   ￭ command-line exec string
   2 | axiom B : A → Type
     ^ constant A is or uses a nonparametric axiom, can't be used in a parametric command

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0306"><summary><code>E0306</code> Hidden_variable</summary>

This error is reported when, in a modal type theory, a variable is used in a
place where it is hidden. Some constructs strip the locks at the end of the
context while checking a subterm, and the variables bound to the right of
those locks are removed from the context along with them. Such a variable is
still in scope for the parser, so its name is resolved, but referring to it
raises this error.

Neighboring codes: if the lock to be stripped is not found in the context at
all, ``E1716`` (for a ``let only`` lock) or ``E1707`` (for a key) is reported;
if the variable is still in the context but lies behind a lock, other errors
from the ``E17xx`` family are reported. The old code ``E0303`` is no longer
raised.

**Example**

Run this example with the ``-coreflector`` flag. The argument of ``♭.`` is
checked under a ``♭`` lock, and ``z`` is bound after that lock. While the
bound term of the ``let only`` is checked, the ``lock ♭`` clause removes that
lock, and ``z`` with it, so ``z`` cannot be used there.

.. code-block:: none

   def ♭ (A :♭| Type) : Type ≔ data [ ♭. (x :♭| A) ]
   def k : ♭ (Type → Type) ≔ ♭. (z ↦ let only w : Type ≔ z and lock ♭ in w)

   ￫ error[E0306]
   ￭ command-line exec string
   2 | def k : ♭ (Type → Type) ≔ ♭. (z ↦ let only w : Type ≔ z and lock ♭ in w)
     ^ variable hidden by lock

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E04xx: Bidirectional typechecking and case trees</h2>

.. raw:: html

   <details class="error-code" id="E0400"><summary><code>E0400</code> Nonsynthesizing</summary>

This error is reported when a term whose type cannot be inferred appears in a
position where Narya has to find its type by itself. Narya uses bidirectional
typechecking: some terms, such as variables and applications, *synthesize*
their type, while others, such as abstractions, tuples and constructors, can
only be *checked* against a type that is already known. This error arises when
a term of the second kind is written where the type is not known in advance.
The message names the position in parentheses.

If the term does synthesize but its type does not match the expected one, the
error is ``E0401``; a mode that cannot be synthesized has a separate code
(``E1703``).

**Examples**

An abstraction given directly to ``echo``, which needs to synthesize the type
of its argument:

.. code-block:: none

   echo (x ↦ x)

   ￫ error[E0400]
   ￮ non-synthesizing term in synthesizing position (argument of echo)

The same abstraction as the argument of a degeneracy. Here the position named
in the message is the argument of ``refl`` rather than that of ``echo``, and
the error carries a source location:

.. code-block:: none

   echo (refl (x |-> x))

   ￫ error[E0400]
   ￭ command-line exec string
   1 | echo (refl (x |-> x))
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0401"><summary><code>E0401</code> Unequal_synthesized_type</summary>

This error is reported when a term synthesizes one type but is being checked
against a different one, and the two are not definitionally equal. The message
shows both types and the first subterms at which they differ.

This error arises mainly when the term synthesizes. Checking terms such as
abstractions, tuples and constructors give their own codes when they are
checked against a type of the wrong form (for example ``E0700`` for an
abstraction checked against a non-function type). One exception is a
constructor of an indexed datatype: if the indices of the type it produces
differ from those of the type it is checked against, as when ``rfl.`` is
checked against ``Jd A a b``, this error is reported. Writing something that is
not a type where a type is required usually ends up here as well: in
``(a : Id A)``, ``Id A`` synthesizes the type ``Type⁽ᵉ⁾ A A`` and cannot be
checked against ``Type``. For higher-dimensional applications, a mismatch in
the types of the boundary arguments has a separate code (``E0704``).

**Example**

.. code-block:: none

   axiom A : Type
   axiom B : Type
   axiom a : A
   echo (a : B)

   ￫ error[E0401]
   ￭ command-line exec string
   4 | echo (a : B)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0402"><summary><code>E0402</code> Synthesizing_recursion</summary>

This error is reported when, in a mutual ``def … and …``, a constant defined
without a declared type is used before its own body has been checked: in the
body of an earlier constant in the block that has a declared type, or in the
declared type or parameters of a later constant in the block, since all
declared types and parameters are checked before any body. A constant can only
be referred to before its own body is checked if its type has been declared.
The order matters: using an untyped constant in a later body is accepted,
since its type has been synthesized by then. (If the untyped constant is used
in the declared type or parameters of an earlier constant, or in the body of
an earlier constant that is itself untyped, or if it refers to itself in its
own body, the name is not yet in scope and the error is ``E0300`` instead.)

**Example**

.. code-block:: none

   def f : Type ≔ g
   and g ≔ f

   ￫ error[E0402]
   ￭ command-line exec string
   1 | def f : Type ≔ g
     ^ for 'g' to be recursive, it must have a declared type

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0404"><summary><code>E0404</code> Invalid_synthesized_type</summary>

This error is reported when a ``match`` in a synthesizing position takes its
type from its first branch that synthesizes, but that type depends on the
pattern variables of that branch and therefore cannot be the type of the whole
``match``.

A ``match`` is normally checked against a known type. In a synthesizing
position, for example as the head of an application, Narya instead takes the
type synthesized by the first branch whose body synthesizes and checks the
remaining branches against it. That branch is checked in a context extended by
its pattern variables, so a type that mentions them is meaningless outside the
branch. If a dependent result type is wanted, the ``match`` must be in a
checking position.

Neighboring codes: if no branch synthesizes, ``E0400`` is reported; if the
synthesized type is valid but other branches do not match it, the errors are
the ordinary ones in those branches (for example ``E0401``).

**Example**

Here the ``match`` is the head of an application, so it has to synthesize. The
first branch is an abstraction and does not synthesize; the second synthesizes
``T x``, but ``x`` exists only in the ``suc. x`` branch.

.. code-block:: none

   def N : Type ≔ data [ zero. | suc. (_ : N) ]
   def Bool : Type ≔ data [ true. | false. ]
   def T (n : N) : Type ≔ match n [ zero. ↦ N | suc. _ ↦ Bool ]
   axiom g : (n : N) → T n
   def k (n : N) : Bool ≔ (match n [ zero. ↦ y ↦ true. | suc. x ↦ g x ]) zero.

   ￫ error[E0404]
   ￭ command-line exec string
   5 | def k (n : N) : Bool ≔ (match n [ zero. ↦ y ↦ true. | suc. x ↦ g x ]) zero.
     ^ type T x synthesized by synthesizing branch of match is invalid for entire term

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0405"><summary><code>E0405</code> Type_expected</summary>

This error is reported when, during typechecking, a value that Narya needs to
inspect as a type does not have the form of a type at all. The message has the
form ``expected type while …, got …``: the first part says during which
operation this happens (for example ``typechecking lambda``, ``typechecking
tuple``, or ``synthesizing application spine``), and the second part shows the
offending value.

To find out what kind of type something is (a pi-type, a universe, a datatype,
a record or codata type, or a neutral type), Narya expects it to be a
canonical type or a neutral term; this error is raised when it is instead an
abstraction, a tuple or a constructor. For a type that is only partially
instantiated the error is ``E0504`` instead, and for a type that has already
failed it is the silent ``E0002``. The severity depends on the situation: it
is a user error when a term written by the user is being checked against a
type given by the user, and a bug in Narya otherwise, since then the "type"
was produced by Narya itself. In practice, no way has been found to reach
this error with user input.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E05xx: Dimensions</h2>

.. raw:: html

   <details class="error-code" id="E0500"><summary><code>E0500</code> Dimension_mismatch</summary>

This error is reported when two dimensions that Narya expects to be equal turn
out to be different during an internal operation. The message has the form
``dimension mismatch in … (… ≠ …)``, and names the operation and the two
dimensions. This is an internal consistency check: dimension mistakes in user
code are reported with other codes, such as ``E0501``, ``E0502``, ``E0503``,
``E0703``, ``E0601`` and ``E0602``. Seeing it indicates a bug in Narya, which
should be reported to the developers.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0501"><summary><code>E0501</code> Not_enough_lambdas</summary>

This error is reported when an ordinary abstraction (``↦``) is checked against
a higher-dimensional function type but does not bind enough variables. A
higher-dimensional function takes a whole cube of arguments, and with ``↦``
each face of that cube needs its own variable: the boundary faces implicitly,
in braces, and the top face explicitly, as in ``{x₀} {x₁} x₂ ↦ …`` for a
one-dimensional function. The message says how many more variables are needed.
A cube abstraction ``x ⤇ …`` binds the whole cube with a single name instead.

Neighboring codes: if the number of variables is right but one of them is
explicit where an implicit one is expected, or conversely, the error is
``E0702``. Too few arguments in an application of such a function is
``E0502``, and errors about ``⤇`` itself are ``E0508`` and ``E0509``.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   echo (({x} {y} |-> x) : Id (A -> A) f f)

   ￫ error[E0501]
   ￭ command-line exec string
   3 | echo (({x} {y} |-> x) : Id (A -> A) f f)
     ^ not enough non-cube variables for higher-dimensional abstraction: need 1 more

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0502"><summary><code>E0502</code> Not_enough_arguments_to_function</summary>

This error is reported when a higher-dimensional function, such as ``refl f``,
is applied to too few arguments. Such a function takes a cube of arguments at
once: the boundary arguments implicitly, in braces, followed by the explicit
primary argument, as in ``refl f {a₀} {a₁} a₂``. If the first argument is
explicit, the boundary is inferred from its type; if it is implicit, Narya
expects the whole cube to be written out, and this error arises when the
argument list ends before the cube is complete.

Neighboring codes: ``E0703`` if the primary argument is given explicitly but
its dimension is too low, ``E0400`` if it does not synthesize, and ``E0702``
if implicit and explicit arguments are in the wrong order. The same shortage
is ``E0503`` when instantiating a type and ``E0507`` for a constructor.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom a : A
   echo (refl f {a})

   ￫ error[E0502]
   ￭ command-line exec string
   4 | echo (refl f {a})
     ^ not enough arguments for a higher-dimensional function application

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0503"><summary><code>E0503</code> Not_enough_arguments_to_instantiation</summary>

This error is reported when a higher-dimensional type is instantiated with too
few arguments. Each dimension of instantiation needs all of its boundary
arguments at once: for example ``Id A`` needs two elements of ``A``, so ``Id A
a`` is incomplete. An uninstantiated type such as ``Id A`` is a valid term on
its own.

Neighboring codes: ``E0505`` if the type is not higher-dimensional, ``E0701``
if the head is neither a function nor a type, ``E0502`` for too few arguments
to a higher-dimensional function, and ``E0708`` if an ordinary argument is
given under nullary parametricity.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom a : A
   echo (Id A a)

   ￫ error[E0503]
   ￭ command-line exec string
   4 | echo (Id A a)
     ^ not enough arguments to instantiate a higher-dimensional type

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0504"><summary><code>E0504</code> Type_not_fully_instantiated</summary>

This error is reported when a term is checked against, or a field is projected
from a term of, a higher-dimensional type that has not been given all of its
boundary arguments, for instance ``Id A`` rather than ``Id A x y``. Only fully
instantiated types have elements. The message has the form ``type not fully
instantiated in … (need … more dimensions)``. A partially instantiated type
that the user writes where a type is expected is normally rejected earlier, as
a type mismatch ``E0401``, so this error is rarely seen. Depending on where it
is detected, it is reported as an error or as a bug in Narya.

Neighboring codes: ``E0503`` for an instantiation that is written with too few
arguments, and ``E0405`` if the value is not a type at all.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0505"><summary><code>E0505</code> Instantiating_zero_dimensional_type</summary>

This error is reported when a type that is not higher-dimensional is applied
to an argument. Application syntax means function application when the head
has a function type, and instantiation with boundary arguments when the head
is a higher-dimensional type, as in ``Id A a b``. An ordinary zero-dimensional
type has no boundary to supply and is not a function either. The same error
arises when a fully instantiated type is given one more argument.

Neighboring codes: ``E0701`` if the head is neither a function nor a type, as
in ``a b``; ``E0503`` if the head is a higher-dimensional type but there are
too few arguments.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom a : A
   echo A a

   ￫ error[E0505]
   ￭ command-line exec string
   4 | echo A a
     ^ can't apply/instantiate a zero-dimensional type A

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0506"><summary><code>E0506</code> Invalid_variable_face</summary>

This error is reported when a face suffix such as ``x.0`` is used on a
variable that has no such face. Face suffixes are meaningful only for cube
variables, which are bound by a cube abstraction ``⤇``, by a
higher-dimensional ``match`` or ``let only``, or as the self variable of a
higher field. The suffix must have exactly as many digits as the dimension of
the variable, so an ordinary zero-dimensional variable has no faces. The
message gives the dimension of the variable and the face that is asked for.

Neighboring codes: a suffix with a digit beyond the arity is not read as a
face at all, and gives ``E0300``. Mistakes with ``⤇`` itself are ``E0508``,
``E0509`` and ``E0510``.

**Example**

.. code-block:: none

   axiom A : Type
   echo ((x ↦ x.0) : A -> A)

   ￫ error[E0506]
   ￭ command-line exec string
   2 | echo ((x ↦ x.0) : A -> A)
     ^ invalid face: variable of dimension 0 has no face '0'

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0507"><summary><code>E0507</code> Not_enough_arguments_to_constructor</summary>

This error is reported when a constructor is checked against a
higher-dimensional instance of a datatype, and its optional boundary arguments
in braces are started, but the argument list ends before all of them are
given. For each argument of the constructor, either all of its boundary faces
are given in braces before the explicit top-dimensional argument, or none of
them.

Neighboring codes: ``E0702`` if an explicit argument comes before the boundary
is complete, ``E1004`` if a supplied boundary argument differs from the one
determined by the type, and ``E1001`` if the number of explicit arguments is
wrong.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   echo (suc. {zero.} : Id ℕ (suc. zero.) (suc. zero.))

   ￫ error[E0507]
   ￭ command-line exec string
   2 | echo (suc. {zero.} : Id ℕ (suc. zero.) (suc. zero.))
     ^ not enough arguments to a higher-dimensional constructor application

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0508"><summary><code>E0508</code> Zero_dimensional_cube_abstraction</summary>

This error is reported when a cube abstraction ``⤇`` is used where nothing is
higher-dimensional: in an abstraction checked against an ordinary function
type, in a branch of a zero-dimensional ``match``, or in a clause of a
zero-dimensional comatch. The last word of the message says which of these is
the case. The ordinary ``↦`` is used there instead. Checking continues after
this error, so it can be reported several times, or together with other
errors.

In a multiple match that combines a higher-dimensional discriminee with a
zero-dimensional one, ``⤇`` is meant to be accepted. Narya currently reports
this error for some branches of such a match when the higher-dimensional
discriminee comes first; this is a bug in Narya.

Neighboring codes: the opposite mistakes are ``E0501``, too few variables with
``↦`` against a higher-dimensional function type, and ``E0510``, ``↦`` binding
a cube variable in a higher-dimensional match. Variables of different
dimensions under one ``⤇`` give ``E0509``.

**Example**

.. code-block:: none

   axiom A:Type
   def prod (X Y : Type) : Type ≔ sig (fst:X,snd:Y)
   def f : prod (A→A) (A→A) ≔ (x ⤇ x, x ⤇ x)

   ￫ error[E0508]
   ￭ command-line exec string
   3 | def f : prod (A→A) (A→A) ≔ (x ⤇ x, x ⤇ x)
     ^ cube abstraction not allowed for zero-dimensional function

   ￫ error[E0508]
   ￭ command-line exec string
   3 | def f : prod (A→A) (A→A) ≔ (x ⤇ x, x ⤇ x)
     ^ cube abstraction not allowed for zero-dimensional function

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0509"><summary><code>E0509</code> Mismatched_dimensions_in_cube_abstraction</summary>

This error is reported when several variables are bound by a single cube
abstraction ``x y ⤇ …``, but the function types they belong to have different
dimensions. All variables that share one ``⤇`` must be cubes of the same
dimension; when the dimensions differ, nested abstractions ``x ⤇ y ⤇ …`` can
be written instead. The message gives the two dimensions, and a second mark
shows the previous variable. Checking continues after this error.

Neighboring codes: ``E0508`` if ``⤇`` is used against a zero-dimensional
function type, ``E0501`` if ``↦`` does not bind enough variables for a
higher-dimensional function, and ``E0506`` for a wrong face suffix on a cube
variable.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom h : A → Id (A → A) f f
   echo ((x y ⤇ refl h x.2 y.22) : Id (A → Id (A → A) f f) h h)

   ￫ error[E0509]
   ￭ command-line exec string
   4 | echo ((x y ⤇ refl h x.2 y.22) : Id (A → Id (A → A) f f) h h)
     ^ previous variable
     ^ can't combine cube abstractions of different dimensions: e ≠ ee

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0510"><summary><code>E0510</code> Noncube_abstraction_in_higher_dimensional_match</summary>

This error is reported when a ``match`` on an element of a higher-dimensional
datatype, for example ``p : Id ℕ x y``, has a branch written with ``↦`` that
leaves a pattern variable as a cube. In such a match each argument of a
constructor is a cube. A branch names it either with a single cube variable,
which requires ``⤇``, or by naming all of its faces, with the boundary faces
in braces, which uses ``↦``. Branches that bind no variables may also use
``↦``. Checking continues after this error.

Neighboring codes: the opposite mistake, ``⤇`` in a zero-dimensional match, is
``E0508``. A wrong number of boundary variables in braces is ``E1311``, and a
wrong number of patterns for a constructor is ``E1303``.

**Example**

Here ``a2`` is given with its boundary faces, but ``b`` is left as a cube:

.. code-block:: none

   def P : Type ≔ data [ pair. (x : P) (y : P) ]
   def bad (y0 y1 : P) (y2 : Id P y0 y1) : P ≔ match y2 [ pair. {a0} {a1} a2 b ↦ a0 ]

   ￫ error[E0510]
   ￭ command-line exec string
   2 | def bad (y0 y1 : P) (y2 : Id P y0 y1) : P ≔ match y2 [ pair. {a0} {a1} a2 b ↦ a0 ]
     ^ e-dimensional match requires cube abstraction

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E06xx: Degeneracies</h2>

.. raw:: html

   <details class="error-code" id="E0600"><summary><code>E0600</code> Missing_argument_of_degeneracy</summary>

This error is reported when a degeneracy such as ``refl`` or ``sym`` is
written without the term it should act on. Degeneracies are not first-class
functions: they must always be applied to an argument, and cannot be passed to
another function. A local variable with the same name takes precedence. Narya
reports the error and goes on checking the rest of the term.

Neighboring codes: ``E0206`` for an invalid degeneracy in a superscript,
``E0601`` and ``E0602`` if a degeneracy has an argument but a dimension is too
low, and ``E0400`` if its argument does not synthesize.

**Example**

.. code-block:: none

   echo refl

   ￫ error[E0600]
   ￭ command-line exec string
   1 | echo refl
     ^ missing argument for degeneracy refl

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0601"><summary><code>E0601</code> Low_dimensional_argument_of_degeneracy</summary>

This error is reported when a degeneracy is applied to a term whose dimension
is too low for it. For example ``sym`` permutes the two directions of a
square, so its argument must be at least two-dimensional. The message says
that the dimension of the argument "does not factor through" the dimension
that the degeneracy requires. For a symmetry such as ``sym`` applied to a
non-synthesizing term, such as a constructor, the dimension is taken from the
type that it is checked against, and this error is reported if that type is
too low-dimensional.

Neighboring codes: ``E0602`` if a dimension-adding degeneracy such as
``refl``, applied to a non-synthesizing term, is checked against a type of too
low a dimension; ``E0600`` if the degeneracy has no argument; and ``E0703`` if
the primary argument of a higher-dimensional application has too low a
dimension.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom a : A
   echo sym f

   ￫ error[E0601]
   ￭ command-line exec string
   4 | echo sym f
     ^ insufficient dimension for argument of degeneracy 'sym':
        0 does not factor through ee

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0602"><summary><code>E0602</code> Low_dimensional_type_of_degeneracy</summary>

This error is reported when a dimension-adding degeneracy such as ``refl``,
applied to a non-synthesizing term such as a constructor, is checked against a
type whose dimension is too low to be the type of that degeneracy. (For a
symmetry such as ``sym``, the same situation is reported as ``E0601``.) For
example ``refl M`` can only be checked against a type of dimension at least
one, such as ``Id A x y``. If the argument does synthesize, the same mistake
is reported as an ordinary type mismatch ``E0401``.

Neighboring codes: ``E0601`` if it is the argument of the degeneracy whose
dimension is too low, and ``E0600`` if the degeneracy has no argument at all.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   echo (refl zero. : ℕ)

   ￫ error[E0602]
   ￭ command-line exec string
   2 | echo (refl zero. : ℕ)
     ^ insufficient dimension for expected type of degeneracy 'refl':
        0 does not factor through e

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E07xx: Function types</h2>

.. raw:: html

   <details class="error-code" id="E0700"><summary><code>E0700</code> Checking_lambda_at_nonfunction</summary>

This error is reported when an abstraction ``x ↦ M`` is checked against a type
that is not a function type. This also happens when an abstraction binds more
variables than the function type has arguments: the remaining abstraction is
then checked against the codomain, which is the type shown in the message.

Neighboring codes: against a higher-dimensional function type, a wrong number
or implicitness of variables gives ``E0501`` or ``E0702`` instead. The
counterparts of this error for the other checking terms are ``E0900`` for
tuples and ``E1400`` for comatches.

**Examples**

An abstraction against a type that is not a function type:

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom a : A
   echo ((x ↦ x) : A)

   ￫ error[E0700]
   ￭ command-line exec string
   4 | echo ((x ↦ x) : A)
     ^ checking abstraction against non-function type A

One variable too many for a one-dimensional function type:

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   echo (({x0} {x1} x2 x3 ↦ refl f x0 x1 x2) : Id (A -> A) f f)

   ￫ error[E0700]
   ￭ command-line exec string
   3 | echo (({x0} {x1} x2 x3 ↦ refl f x0 x1 x2) : Id (A -> A) f f)
     ^ checking abstraction against non-function type Id A (f x0) (f x1)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0701"><summary><code>E0701</code> Applying_nonfunction_nontype</summary>

This error is reported when a term is applied to an argument, but its type is
neither a function type nor a universe, so it can be neither applied as a
function nor instantiated as a higher-dimensional type. A common cause is
giving a function more arguments than it accepts. The message shows the term
that is being applied, which may be only the first part of the application,
together with its type.

Neighboring codes: ``E0505`` if the term applied is a type that is not
higher-dimensional or is already fully instantiated, ``E0707`` if a function
or a higher-dimensional type is given a dot as its argument, and ``E0502`` and
``E0503`` if there are too few arguments.

**Example**

Here ``refl f (refl a)`` is complete, and the last argument is one too many:

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom a : A
   echo (refl f (refl a) a)

   ￫ error[E0701]
   ￭ command-line exec string
   4 | echo (refl f (refl a) a)
     ^ attempt to apply/instantiate
         ap f (refl a)
       of type
         Id A (f a) (f a)
       which is not a function-type or universe

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0702"><summary><code>E0702</code> Unexpected_implicitness</summary>

This error is reported when an argument, abstraction variable or domain is
written explicitly where an implicit one, in braces, is required, or
conversely. In higher-dimensional function types, applications and
constructors, the boundary components are implicit and the top-dimensional
(primary) one is explicit. Braces are not allowed on the argument of an
ordinary function or of a zero-dimensional constructor. The message says which
was expected.

Neighboring codes: ``E0501``, ``E0502`` and ``E0503`` if there are too few
variables or arguments; ``E0703`` and ``E0704`` if the boundary is inferred
from the primary argument and does not fit; and ``E1004`` if a boundary
argument of a constructor does not match the type.

**Examples**

An ordinary abstraction against a one-dimensional function type, where the
first variable must be implicit:

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom a : A
   echo ((x ↦ x) : Id (A → A) f f)

   ￫ error[E0702]
   ￭ command-line exec string
   4 | echo ((x ↦ x) : Id (A → A) f f)
     ^ unexpected explicit abstraction: expecting implicit variable

An implicit argument for a zero-dimensional constructor:

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   axiom n₀ : ℕ
   def bad : ℕ ≔ suc. {n₀} n₀

   ￫ error[E0702]
   ￭ command-line exec string
   3 | def bad : ℕ ≔ suc. {n₀} n₀
     ^ unexpected implicit argument: expecting explicit primary argument of constructor suc

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0703"><summary><code>E0703</code> Insufficient_dimension</summary>

This error is reported when a higher-dimensional function is applied to an
explicit primary argument without its implicit boundary arguments, so Narya
reads the boundary off the type of that argument, but the dimension of the
argument is too low for that. For example ``refl f`` expects an element of
some ``Id A x y``, not a point of ``A``. The message says that the dimension
of the argument "does not factor through" the dimension of the application.
The same error arises when a higher-dimensional type is instantiated in this
way, as in ``Id (Id A) a a a2 a2 a2`` where the first two arguments should be
elements of ``Id A a a``; the message then says ``for instantiation``.

Neighboring codes: ``E0704`` if the dimension suffices but a boundary
component that is read off has the wrong type, ``E0400`` if the primary
argument does not synthesize, and ``E0601`` for the argument of a degeneracy.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom a : A
   echo refl f a

   ￫ error[E0703]
   ￭ command-line exec string
   4 | echo refl f a
     ^ insufficient dimension of primary argument for higher-dimensional application:
       0 does not factor through e

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0704"><summary><code>E0704</code> Unequal_synthesized_boundary</summary>

This error is reported when a higher-dimensional function is applied to its
primary argument only, so the boundary arguments are read off the type of that
argument, but one of these boundary components does not have the type that the
function expects. The message names the face of the boundary concerned and
shows the two types that differ. The same error arises when a
higher-dimensional type is instantiated with its boundary arguments left
implicit.

Neighboring codes: ``E0703`` if the dimension of the primary argument is too
low for a boundary to be read off. If the boundary arguments are written
explicitly in braces, the same mismatch is an ordinary ``E0401``. For
constructors, a wrong boundary argument is ``E1004``.

**Example**

.. code-block:: none

   axiom X : Type
   axiom Y : Type
   axiom g : Y → Y
   axiom x : X
   echo refl g (refl x)

   ￫ error[E0704]
   ￭ command-line exec string
   5 | echo refl g (refl x)
     ^ the 0-boundary synthesized type
         X
       but is being checked against type
         Y
       unequal head constants:
         X
       does not equal
         Y

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0705"><summary><code>E0705</code> Not_enough_domains</summary>

This error is reported when a higher-dimensional function type written with
``→⁽ᵉ⁾``, or a higher superscript, does not list enough domains. Such a type
needs one domain for every face of the cube: for dimension ``e``, two implicit
domains for the endpoints and then the explicit primary domain, as in ``{x₀ x₁
: A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ …``. Implicit domains are collected up to the
first explicit one, which closes the group, so writing the endpoints in
ordinary parentheses also gives this error.

Neighboring codes: ``E0706`` if the domains are malformed, for instance with a
wrong boundary, an extra implicit domain, or a dependence on a variable that
is not available; ``E0702`` if there is no explicit primary domain; and
``E0501`` for too few variables in an abstraction.

**Example**

.. code-block:: none

   axiom A : Type
   axiom a : A
   echo (x₂ : Id A a a) →⁽ᵉ⁾ Id A a a

   ￫ error[E0705]
   ￭ command-line exec string
   3 | echo (x₂ : Id A a a) →⁽ᵉ⁾ Id A a a
     ^ not enough domains for an e-dimensional function type

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0706"><summary><code>E0706</code> Invalid_higher_function</summary>

This error is reported when a higher-dimensional function type written with
``→⁽ᵉ⁾`` is not well-formed; the message says which part is at fault. Each
higher domain must be an instantiation of a higher-dimensional type whose
boundary arguments are exactly the previously bound variables. The codomain
must also be fully instantiated, but its boundary arguments may be arbitrary
terms. There must not be too many domains, and the domains and the codomain
may only use the variables that are available to them.

Neighboring codes: ``E0705`` if there are too few domains, and ``E0702`` if
there is no explicit primary domain.

**Example**

Here the second boundary argument of the primary domain should be ``x₁``:

.. code-block:: none

   axiom A : Type
   echo {x₀ x₁ : A} (x₂ : Id A x₀ x₀) →⁽ᵉ⁾ Id A x₀ x₁

   ￫ error[E0706]
   ￭ command-line exec string
   2 | echo {x₀ x₁ : A} (x₂ : Id A x₀ x₀) →⁽ᵉ⁾ Id A x₀ x₁
     ^ invalid higher function-type: invalid domain boundary

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0707"><summary><code>E0707</code> Invalid_nullary_application</summary>

This error is reported when the dot ``.`` that denotes zero arguments is used
where it is not allowed. An application ``M .`` is only meaningful for
instantiating a higher-dimensional type under nullary parametricity
(``-parametric -arity 0``), where a dimension has no endpoints. Applying a
function to it, as in ``f .``, or writing ``Id A .`` when the arity is not
zero, gives this error.

Neighboring codes: ``E0708`` is the reverse, an ordinary argument where the
dot is expected. If the term before the dot cannot be applied at all, the
error is ``E0701``.

**Example**

.. code-block:: none

   axiom A : Type
   echo Id A .

   ￫ error[E0707]
   ￭ command-line exec string
   2 | echo Id A .
     ^ invalid nullary application

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0708"><summary><code>E0708</code> Expected_nullary_application</summary>

This error is reported when, under nullary parametricity (``-parametric -arity
0``), a higher-dimensional type is applied to an ordinary argument. With arity
0 a dimension has no endpoints, so an instantiation takes no arguments and is
written as an application to a dot, as in ``Id A .``.

Neighboring codes: ``E0707`` is the reverse, a dot where it is not allowed.
With other arities, too few arguments in an instantiation give ``E0503``, and
an extra argument for a fully instantiated type gives ``E0505``.

**Example**

Run this example with the flags ``-parametric -arity 0``.

.. code-block:: none

   axiom A : Type
   axiom a : A
   echo Id A a

   ￫ error[E0708]
   ￭ command-line exec string
   3 | echo Id A a
     ^ expected nullary application

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0709"><summary><code>E0709</code> Invalid_higher_letonly</summary>

This error is reported when a higher-dimensional ``let only`` binding is not
valid; the message gives the reason. Most often the declared type of the
variable is an uninstantiated higher-dimensional type such as ``Id B``, so the
variable is a cube whose boundary is read off the type of the bound term, but
that type has too low a dimension. See :ref:`Higher-dimensional let-only`.

Neighboring codes: ``E0400`` if the bound term does not synthesize, ``E1500``
if the declared type does not belong to a universe, and ``E0401`` if the
dimension suffices but the types differ. The analogous error for an
application is ``E0703``.

**Example**

.. code-block:: none

   axiom B : Type
   axiom b0 : B
   synth let only x : Id B ≔ b0 in x

   ￫ error[E0709]
   ￭ command-line exec string
   3 | synth let only x : Id B ≔ b0 in x
     ^ invalid higher-dimensional let-only: bound term has a type of dimension 0, which isn't an instantiation of a type of dimension e

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E08xx: Record fields</h2>

.. raw:: html

   <details class="error-code" id="E0800"><summary><code>E0800</code> No_such_field</summary>

This error is reported when a field is projected from a term whose type has no
field of that name. The type may be a record type or codatatype that lacks the
field, in which case the message names that type, or not a record type or
codatatype at all, in which case the message names the term instead (``term a
has no field named …``). For a record type that is itself higher-dimensional,
such as ``Gel``, an instance with a nonidentity degeneracy such as ``sym``
applied to it is not treated as a record type, and has no fields.

Neighboring codes: ``E0801`` if the field exists but the numeric suffix does
not fit it, ``E0802`` if the suffix is not valid for the dimension of the
term, ``E0903`` for a tuple component that is not a field, and ``E1712`` and
``E1713`` for modal fields.

**Example**

.. code-block:: none

   def R : Type ≔ sig ( fst : Type, snd : Type )
   axiom s : R
   echo (s .third)

   ￫ error[E0800]
   ￭ command-line exec string
   3 | echo (s .third)
     ^ record type R has no field named third

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0801"><summary><code>E0801</code> Wrong_dimension_of_field</summary>

This error is reported when a field with this name exists, but the numeric
suffix on the projection does not fit it. The suffix selects which directions
of a higher-dimensional term belong to the field itself, so its length must
equal the intrinsic dimension of the field: an ordinary field takes no suffix,
even when it is projected from a higher-dimensional term, while a higher field
needs one. The only exception is that the suffix ``.1`` of a one-dimensional
field may be omitted when the term is also one-dimensional.

Neighboring codes: ``E0800`` if there is no field of that name, and ``E0802``
if the digits of the suffix are not valid for the dimension of the term.

**Example**

.. code-block:: none

   def R : Type ≔ sig ( x : Type )
   axiom a : R
   axiom c : Id R a a
   echo c .x.1

   ￫ error[E0801]
   ￭ command-line exec string
   4 | echo c .x.1
     ^ field x of record type
         R⁽ᵉ⁾ a a
       has intrinsic dimension 0 and used at dimension e, can't have suffix .1

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0802"><summary><code>E0802</code> Invalid_field_suffix</summary>

This error is reported when the numeric suffix on a field projection is not
meaningful for the dimension of the term that is projected from. Each digit of
a suffix refers to a direction of that term, so it must be between 1 and the
dimension of the term, and no digit may be repeated; a zero-dimensional term
admits no suffix at all. This is checked before the field name is looked up.

Neighboring codes: ``E0801`` if the suffix is valid for the term but does not
fit the field, ``E0800`` if there is no field of that name, and ``E0506`` for
face suffixes on variables.

**Example**

.. code-block:: none

   def R : Type ≔ sig ( x : Type )
   axiom a : R
   echo a .x.1

   ￫ error[E0802]
   ￭ command-line exec string
   3 | echo a .x.1
     ^ invalid suffix .1 for field x of 0-dimensional type R

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E09xx: Tuples</h2>

.. raw:: html

   <details class="error-code" id="E0900"><summary><code>E0900</code> Checking_tuple_at_nonrecord</summary>

This error is reported when a tuple ``(…, …)`` is checked against a type that
is not a record type. Tuples do not synthesize, so they can only be used where
the expected type is a record type defined with ``sig``. Elements of a
codatatype are built with a comatch instead.

Neighboring codes: ``E0400`` if there is no expected type at all, ``E0901`` if
the expected type is a record type with a nonidentity degeneracy applied, and
``E0902`` to ``E0905`` if the components do not match the fields. The
counterparts for the other checking terms are ``E0700`` for abstractions and
``E1400`` for comatches.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   axiom A : Type
   axiom a : A
   echo (( fst ≔ a ) : ℕ)

   ￫ error[E0900]
   ￭ command-line exec string
   4 | echo (( fst ≔ a ) : ℕ)
     ^ checking tuple against non-record type ℕ

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0901"><summary><code>E0901</code> Checking_tuple_at_degenerated_record</summary>

This error is reported when a tuple is checked against a higher-dimensional
instance of a record type to which a nonidentity degeneracy, such as ``sym``,
is applied. This arises only for record types that are themselves
higher-dimensional, such as ``Gel``: for ordinary record types, degeneracies
reduce to record types of the same form.

Neighboring codes: the same restriction is ``E0800`` for field projections and
``E1401`` for comatches. If the expected type is not a record type at all, the
error is ``E0900``.

**Example**

Run this example with the ``-parametric`` flag. The type ``T`` is an instance
of ``Gel`` with ``sym`` applied to it.

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig ( x .ungel : R x.0 x.1 )
   axiom A : Type
   axiom R : A → A → Type
   axiom a : A
   axiom r : R a a
   def T ≔ sym (refl Gel (refl A) (refl A) (refl R)) {a} {a} (ungel ≔ r) {a} {a} (ungel ≔ r) (refl a) (refl a)
   def t : T ≔ (ungel ≔ refl r)

   ￫ error[E0901]
   ￭ command-line exec string
   7 | def t : T ≔ (ungel ≔ refl r)
     ^ can't check a tuple against a record Gel with a nonidentity degeneracy applied

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0902"><summary><code>E0902</code> Missing_field_in_tuple</summary>

This error is reported when a tuple does not supply a value for one of the
fields of the record type it is checked against. Every field must be given,
either with a label ``fld ≔ value`` or by position; unlabeled components are
assigned, in order, to the fields that have no labeled component. The field is
marked as failed and checking continues, so every missing field is reported.

Neighboring codes: ``E0903`` for an extra component, ``E0904`` for a repeated
label, ``E0905`` for an invalid label, and ``E1402`` for a missing method in a
comatch.

**Example**

.. code-block:: none

   def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )
   axiom A : Type
   axiom a : A
   def t : prod A A ≔ (fst ≔ a)

   ￫ error[E0902]
   ￭ command-line exec string
   4 | def t : prod A A ≔ (fst ≔ a)
     ^ record field 'snd' missing in tuple

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0903"><summary><code>E0903</code> Extra_field_in_tuple</summary>

This error is reported when a tuple has more components than the record type
it is checked against has fields: either a labeled component whose name is not
a field of the record type, or more unlabeled components than there are
remaining fields. Each extra component is reported separately, and checking
continues. A misspelled label typically gives this error together with
``E0902`` for the field that is then missing.

Neighboring codes: ``E0904`` if the same label is given twice, ``E0800`` for
projecting a field that does not exist, and ``E1403`` for an extra method in a
comatch.

**Example**

.. code-block:: none

   def prod (A B : Type) : Type ≔ sig ( fst : A, snd : B )
   axiom A : Type
   axiom a : A
   def t : prod A A ≔ (a, a, a)

   ￫ error[E0903]
   ￭ command-line exec string
   4 | def t : prod A A ≔ (a, a, a)
     ^ too many un-labeled fields in tuple

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0904"><summary><code>E0904</code> Duplicate_field_in_tuple</summary>

This error is reported when the same field label appears more than once in a
tuple. This is detected before typechecking, by looking only at the labels in
the tuple itself, so it is reported even when the expected type is not a
record type.

Neighboring codes: ``E0903`` for too many unlabeled components, ``E0905`` for
an invalid label, ``E1501`` for a field declared twice in a record type, and
``E1404`` for a method defined twice in a comatch.

**Example**

.. code-block:: none

   echo (a ↦ ( fst ≔ a, fst ≔ a ))

   ￫ error[E0904]
   ￭ command-line exec string
   1 | echo (a ↦ ( fst ≔ a, fst ≔ a ))
     ^ record field 'fst' appears more than once in tuple

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0905"><summary><code>E0905</code> Invalid_field_in_tuple</summary>

This error is reported when the left-hand side of a ``≔`` inside a tuple is
not a valid field label. A labeled component has the form ``fld ≔ value``,
where ``fld`` is a single field name, or ``_ ≔ value`` for an unlabeled
component; a parenthesized term, a dotted name or an application is not a
label. This is detected before typechecking.

Neighboring codes: ``E0903`` if the label is well-formed but is not a field of
the record type, and ``E0904`` if a label is repeated.

**Example**

.. code-block:: none

   axiom A : Type
   axiom a : A
   def S : Type ≔ sig ( x : A )
   echo (( (x) ≔ a ) : S)

   ￫ error[E0905]
   ￭ command-line exec string
   4 | echo (( (x) ≔ a ) : S)
     ^ invalid field in tuple

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E10xx: Datatype constructors</h2>

.. raw:: html

   <details class="error-code" id="E1000"><summary><code>E1000</code> No_such_constructor</summary>

This error is reported when a constructor ``c.`` is checked against a type
that has no constructor of that name: either a datatype without such a
constructor, or a type that is not a datatype at all. Constructors do not
synthesize, so their meaning is determined entirely by the type they are
checked against. Numerals are expanded into ``zero.`` and ``suc.``, so a
numeral checked against a type that is not a datatype gives this error too.
Function types are an exception: a constructor checked against a function type
is treated as a function into the codomain, so the error is then about the
codomain, or is ``E1001``.

Neighboring codes: ``E1001`` if the constructor exists but has the wrong
number of arguments, and ``E1301`` for a constructor in a ``match`` pattern
that does not belong to the datatype.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def t : ℕ ≔ two.

   ￫ error[E1000]
   ￭ command-line exec string
   2 | def t : ℕ ≔ two.
     ^ datatype ℕ has no constructor named two

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1001"><summary><code>E1001</code> Wrong_number_of_arguments_to_constructor</summary>

This error is reported when a constructor is applied to too many or too few
arguments compared with its declaration in the datatype. The message says how
many are extra or missing. A constructor with missing arguments is accepted
where a function type is expected (``suc.`` checks against ``ℕ → ℕ``), so the
"not enough" form arises when the expected type is the datatype itself. Extra
arguments are counted whether they are explicit or written in braces.

Neighboring codes: mistakes in the boundary arguments in braces of a
higher-dimensional constructor are ``E0507``, ``E0702`` and ``E1004``. The
same mismatch in a ``match`` pattern is ``E1303``, and a constructor that the
datatype does not have is ``E1000``.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   echo ((suc. ) : ℕ)

   ￫ error[E1001]
   ￭ command-line exec string
   2 | echo ((suc. ) : ℕ)
     ^ not enough arguments to constructor suc (need 1 more)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1002"><summary><code>E1002</code> Missing_instantiation_constructor</summary>

This error is reported when a constructor is checked against a
higher-dimensional instance of a datatype, such as ``Id ℕ a b``, whose
boundary terms are not applications of that same constructor. An element ``c.
…`` of such a type exists only when every boundary term is also built with
``c.``. The message shows the expected constructor and what is found instead.

Neighboring codes: ``E1000`` if the datatype has no such constructor, and
``E1004`` if the boundary is built with the right constructor but an
explicitly written boundary argument does not match it.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def id01 : Id ℕ zero. (suc. zero.) := zero.

   ￫ error[E1002]
   ￭ command-line exec string
   2 | def id01 : Id ℕ zero. (suc. zero.) := zero.
     ^ instantiation arguments of datatype must be matching constructors:
       expected
         zero
       but got
         suc

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1003"><summary><code>E1003</code> Unequal_indices</summary>

This code is reserved for a constructor application whose indices do not agree
with those of the datatype instance it is checked against. The message has the
form ``index … of constructor application doesn't match the corresponding
index … of datatype instance``. In the current source code this error is not
raised anywhere, so users are not expected to see it: such a mismatch is
reported as an ordinary type mismatch ``E0401``.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1004"><summary><code>E1004</code> Unequal_boundary_argument</summary>

This error is reported when a higher-dimensional constructor is given explicit
boundary arguments in braces, and one of them is not equal to the
corresponding boundary that is already determined by the type being checked
against. These arguments are redundant, so when they are supplied they must
agree with the type. The message names the face, shows the two terms and says
why they differ. Checking continues after this error.

Neighboring codes: ``E0507`` if the argument list ends before the boundary is
complete, ``E0702`` if an explicit argument appears where a boundary argument
is expected, ``E1001`` for the number of explicit arguments, and ``E1002`` if
the boundary of the type is not built with the same constructor.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   axiom n₀ : ℕ
   axiom n₁ : ℕ
   axiom n₂ : Id ℕ n₀ n₁
   def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₀} n₂

   ￫ error[E1004]
   ￭ command-line exec string
   5 | def bad : Id ℕ (suc. n₀) (suc. n₁) ≔ suc. {n₀} {n₀} n₂
     ^ supplied 1-boundary argument
         n₀
       doesn't match the one determined by the type
         n₁
       unequal head constants:
         n₀
       does not equal
         n₁

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E11xx: Matches: match variable</h2>

.. raw:: html

   <details class="error-code" id="E1100"><summary><code>E1100</code> Unnamed_variable_in_match</summary>

This code is reserved for a ``match`` on a variable that has no name. The
message is ``unnamed match variable``. In the current source code this error
is not raised anywhere, so users are not expected to see it: matching on
unnamed variables is supported, and happens routinely when deep patterns are
expanded into nested matches.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1101"><summary><code>E1101</code> Matching_wont_refine</summary>

Despite its ``E`` code, this is a hint and does not stop processing. It is
displayed in interactive mode, and for files and ``-e`` strings only with the
``-v`` flag. It says that a ``match`` is treated as a
non-dependent match, so the goal type and the types of other variables are not
specialized in the branches. The message gives the reason in parentheses: for
example the match is in a synthesizing position, the discriminee is let-bound,
or an index of its type is not a distinct free variable. Writing ``match M
return _ ↦ _`` states that this is intended, and silences the hint. See
:ref:`Non-dependent matches`.

**Example**

Run this example with the ``-v`` flag.

.. code-block:: none

   def bool : Type ≔ data [ true. | false. ]
   def not (b : bool) ≔ match b [ true. ↦ (false. : bool) | false. ↦ true. ]

   ￫ info[I0000]
   ￮ constant bool defined

   ￫ hint[E1101]
   ￭ command-line exec string
   2 | def not (b : bool) ≔ match b [ true. ↦ (false. : bool) | false. ↦ true. ]
     ^ match will not refine the goal or context (match in synthesizing position)

   ￫ info[I0000]
   ￮ constant not defined

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1102"><summary><code>E1102</code> Nonrefutable_modal_variable</summary>

Despite its ``E`` code, this is a hint and does not stop processing. It is
displayed in interactive mode, and for files and ``-e`` strings only with the
``-v`` flag. It accompanies a missing-branch error ``E1300`` and explains why
the branch could not be refuted automatically: the omitted constructor has an
argument of an empty type, but the modality annotating that argument cannot be
used as the window of a match, for which it would have to be pellucid or
transparent.

Neighboring codes: ``E1300`` is the error that follows. For a match that is
written explicitly, an unsuitable window modality is ``E1715``.

**Example**

Run this example with the flags ``-v -spatial``.

.. code-block:: none

   def N : Type ≔ data [ zero. | suc. (_ : N) ]
   def Empty : Type ≔ data [ ]
   def D : Type ≔ data [ c0. | c1. (_ :♯| Empty) ]
   def g (x : D) : N ≔ match x [ c0. ↦ zero. ]

   ￫ info[I0000]
   ￮ constant N defined

   ￫ info[I0000]
   ￮ constant Empty defined

   ￫ info[I0000]
   ￮ constant D defined

   ￫ hint[E1102]
   ￭ command-line exec string
   4 | def g (x : D) : N ≔ match x [ c0. ↦ zero. ]
     ^ refutation window modality ♯ must be pellucid or transparent

   ￫ error[E1300]
   ￭ command-line exec string
   4 | def g (x : D) : N ≔ match x [ c0. ↦ zero. ]
     ^ missing match clause for constructor c1

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E12xx: Matches: match type</h2>

.. raw:: html

   <details class="error-code" id="E1200"><summary><code>E1200</code> Matching_on_nondatatype</summary>

This error is reported when the discriminee of a ``match``, or the argument of
a pattern-matching abstraction ``[ … ]``, has a type that is not a datatype.
Only elements of types defined with ``data`` can be matched against: not
elements of an axiom, of a function type, of ``Type``, or of a record type or
codatatype, whose components are accessed with field projections. The message
always says "variable", even when the discriminee is not a variable.

Neighboring codes: an empty match on a datatype that has constructors gives
``E1300`` for each of them, and an explicit refutation that finds no empty
type gives ``E1309``. A constructor checked against a type that is not a
datatype is ``E1000``.

**Example**

.. code-block:: none

   def bool : Type ≔ data [ true. | false. ]
   def foo : Type → bool → bool ≔ [ ]

   ￫ error[E1200]
   ￭ command-line exec string
   2 | def foo : Type → bool → bool ≔ [ ]
     ^ can't match on variable belonging to non-datatype Type

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1201"><summary><code>E1201</code> Matching_datatype_has_degeneracy</summary>

This code is reserved for a ``match`` on an element of a datatype instance to
which a degeneracy is applied. The message has the form ``can't match on
element of datatype … that has a degeneracy applied``. In the current source
code this error is not raised anywhere, so users are not expected to see it: a
discriminee whose type cannot be viewed as a datatype gives ``E1200``.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E13xx: Matches: match branches and motives</h2>

.. raw:: html

   <details class="error-code" id="E1300"><summary><code>E1300</code> Missing_constructor_in_match</summary>

This error is reported when a ``match`` has no branch for one of the
constructors of the datatype of the discriminee. Every constructor needs a
branch, unless Narya can refute it automatically because one of its arguments
belongs to an empty datatype. That search is shallow: the type must be a
datatype with no constructors, and a type whose emptiness would only appear
after further matching does not count. One error is reported for each missing
constructor, and checking continues.

Neighboring codes: ``E1301`` for a branch whose constructor does not belong to
the datatype, and ``E1302`` for two branches for the same constructor. If an
argument of an empty type is found but its modality prevents the refutation,
the hint ``E1102`` precedes this error. A refutation written explicitly with
``.`` that fails is ``E1309``.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def f (n : ℕ) : ℕ ≔ match n [ zero. ↦ zero. ]

   ￫ error[E1300]
   ￭ command-line exec string
   2 | def f (n : ℕ) : ℕ ≔ match n [ zero. ↦ zero. ]
     ^ missing match clause for constructor suc

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1301"><summary><code>E1301</code> No_such_constructor_in_match</summary>

This error is reported when a branch of a ``match`` uses a constructor that
does not belong to the datatype of the discriminee. The message names both the
datatype and the constructor. Constructor names in patterns are resolved only
during typechecking, once the type of the discriminee is known. The offending
branch is reported and ignored, and the other branches are still checked; if
it was meant for another constructor, ``E1300`` is reported for that
constructor as well.

Neighboring codes: ``E1000`` is the counterpart for terms, a constructor
checked against a type that does not have it. If the type of the discriminee
is not a datatype at all, the error is ``E1200``.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def f (n : ℕ) : ℕ ≔ match n [ zero. ↦ zero. | suc. k ↦ k | two. ↦ n ]

   ￫ error[E1301]
   ￭ command-line exec string
   2 | def f (n : ℕ) : ℕ ≔ match n [ zero. ↦ zero. | suc. k ↦ k | two. ↦ n ]
     ^ datatype ℕ being matched against has no constructor two

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1302"><summary><code>E1302</code> Duplicate_constructor_in_match</summary>

This error is reported when the same constructor has more than one branch in a
``match``, with nothing further to distinguish the branches. In a multiple or
deep match several branches may begin with the same constructor, as long as
their remaining patterns differ; but there is no first-match rule, so each
case can be covered by only one branch.

Neighboring codes: ``E1307`` if branches overlap because of variable patterns,
``E1306`` if the same constructor is written with different numbers of
arguments, and ``E1300`` for a constructor with no branch at all.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def f (n : ℕ) : ℕ ≔ match n [ zero. ↦ zero. | suc. k ↦ k | zero. ↦ n ]

   ￫ error[E1302]
   ￭ command-line exec string
   2 | def f (n : ℕ) : ℕ ≔ match n [ zero. ↦ zero. | suc. k ↦ k | zero. ↦ n ]
     ^ constructor zero appears twice in match

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1303"><summary><code>E1303</code> Wrong_number_of_arguments_to_pattern</summary>

This error is reported when a constructor pattern in a ``match`` branch binds
too many or too few arguments compared with the declaration of that
constructor. The message says how many are extra or missing. Every argument of
the constructor needs a pattern; ``_`` can be written for arguments that are
not needed. Checking continues after this error.

Neighboring codes: ``E1306`` if the same constructor is written with different
numbers of arguments in different branches, which is detected earlier;
``E1311`` for a wrong number of boundary variables in braces; and ``E1001``
for the wrong number of arguments to a constructor in a term.

**Example**

.. code-block:: none

   def bool : Type ≔ data [ true. | false. ]
   def foo (x : bool) : bool ≔ match x [ true. ↦ false. | false. y ↦ true. ]

   ￫ error[E1303]
   ￭ command-line exec string
   2 | def foo (x : bool) : bool ≔ match x [ true. ↦ false. | false. y ↦ true. ]
     ^ too many arguments to constructor false in match pattern (1 extra)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1304"><summary><code>E1304</code> Duplicate_pattern_variable</summary>

This error is reported when the same variable name is bound more than once in
the patterns of a single ``match`` branch. Patterns are linear: each name can
be bound at most once in a branch, and repeating a name does not mean that the
two positions must be equal. The placeholder ``_`` may be repeated, different
branches are independent, and shadowing a variable from outside the match is
allowed. This is detected before typechecking.

**Example**

.. code-block:: none

   def prod (A B : Type) : Type ≔ data [ pair. (_:A) (_:B) ]
   def proj1 (A B : Type) (u : prod A B) : A ≔ match u return _ ↦ A [ pair. x x ↦ x ]

   ￫ error[E1304]
   ￭ command-line exec string
   2 | def proj1 (A B : Type) (u : prod A B) : A ≔ match u return _ ↦ A [ pair. x x ↦ x ]
     ^ variable name 'x' used more than once in match patterns

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1305"><summary><code>E1305</code> Wrong_number_of_patterns</summary>

This error is reported when a branch of a multiple ``match`` has fewer
comma-separated patterns than there are discriminees. Every branch gives
exactly one pattern for each discriminee; ``_`` can be written for those that
do not matter.

Neighboring codes: a branch with too many patterns is a parse error ``E0200``.
A wrong number of arguments inside a single constructor pattern is ``E1303``,
and inconsistent patterns for the same constructor are ``E1306``.

**Example**

.. code-block:: none

   def bool : Type ≔ data [ true. | false. ]
   def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | false. ↦ false. ]

   ￫ error[E1305]
   ￭ command-line exec string
   2 | def test (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | false. ↦ false. ]
     ^ wrong number of patterns for match

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1306"><summary><code>E1306</code> Inconsistent_patterns</summary>

This error is reported when different branches of a ``match`` use the same
constructor with patterns of different shapes: with different numbers of
arguments, or with explicit boundary variables in braces in one branch but not
in another. This is detected before typechecking, when the datatype is not yet
known, so only the consistency of the branches with each other is checked.

Neighboring codes: if all branches agree with each other but not with the
declaration of the constructor, the error is ``E1303`` or ``E1311``. A
constructor pattern in one branch and a variable in another at the same
position is ``E1307``.

**Example**

.. code-block:: none

   def bool : Type ≔ data [ true. | false. ]
   def foo (x : bool) : bool ≔ match x [ true. ↦ false. | true. y ↦ true. ]

   ￫ error[E1306]
   ￭ command-line exec string
   2 | def foo (x : bool) : bool ≔ match x [ true. ↦ false. | true. y ↦ true. ]
     ^ inconsistent patterns in match

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1307"><summary><code>E1307</code> Overlapping_patterns</summary>

This error is reported when two branches of a ``match`` can apply to the same
value, typically because one branch uses a variable or ``_`` where another
uses a constructor pattern. There is no first-match rule: at each position,
the branches that agree on the constructors in all earlier positions must
either all use constructor patterns or all use variables, so a catch-all
branch cannot be written. With several discriminees, branches that begin with
different constructors are independent of each other: ``true., true.``,
``true., false.`` and ``false., z`` can be the branches of one match.

Neighboring codes: ``E1302`` if two branches for the same constructor cannot
be told apart, and ``E1306`` if the same constructor is written with different
numbers of arguments.

**Example**

.. code-block:: none

   def bool : Type ≔ data [ true. | false. ]
   def bool.and (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true. , false. ↦ false. | _ , false. ↦ false. ]

   ￫ error[E1307]
   ￭ command-line exec string
   2 | def bool.and (x y : bool) : bool ≔ match x,y [ true. , true. ↦ true. | true. , false. ↦ false. | _ , false. ↦ false. ]
     ^ overlapping patterns in match

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1308"><summary><code>E1308</code> No_remaining_patterns</summary>

This is an internal error, raised while a multiple or deep ``match`` is
expanded into nested matches, when several branches remain but no patterns are
left to distinguish them. For a ``match`` it is caught and reported as
``E1302`` or ``E1307``. For a pattern-matching abstraction ``[ … ]`` whose
branches consist only of variable patterns it currently reaches the user; this
is a bug in Narya. The underlying mistake is the one described under
``E1307``: the branches overlap.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def f : ℕ → ℕ ≔ [ x ↦ x | y ↦ y ]

   ￫ bug[E1308]
   ￭ command-line exec string
   2 | def f : ℕ → ℕ ≔ [ x ↦ x | y ↦ y ]
     ^ no remaining patterns while parsing match

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1309"><summary><code>E1309</code> Invalid_refutation</summary>

This error is reported when a branch is written as a refutation, with the body
``.``, but none of the discriminees or pattern variables available to it
belongs to an empty datatype. The search is shallow: the type must be a
datatype with no constructors.

Neighboring codes: a branch that is simply omitted and cannot be refuted
automatically gives ``E1300``. If the type of the discriminee is not a
datatype at all and the branch contains a constructor pattern, the error is
``E1200``; if its patterns are only variables, it is still this error.

**Example**

.. code-block:: none

   def bool : Type ≔ data [ true. | false. ]
   def neg (x : bool) : bool ≔ match x [ true. ↦ false. | false. ↦ . ]

   ￫ error[E1309]
   ￭ command-line exec string
   2 | def neg (x : bool) : bool ≔ match x [ true. ↦ false. | false. ↦ . ]
     ^ invalid refutation: no discriminee has an empty type

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1310"><summary><code>E1310</code> Wrong_number_of_arguments_to_motive</summary>

This error is reported when a ``match`` whose ``return`` clause has the body
``_``, which marks it as explicitly non-dependent, binds the wrong number of
variables in that clause. There must be one for each index of the datatype
plus one for the discriminee itself; parameters are not counted. The message
says how many are required.

Neighboring codes: a genuine motive ``return x ↦ T`` with the wrong number of
variables is checked as an ordinary abstraction and gives errors such as
``E0700``. If the type of the discriminee is not a datatype, the error is
``E1200``.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def f (n : ℕ) : ℕ ≔ match n return _ _ ↦ _ [ zero. ↦ n | suc. k ↦ k ]

   ￫ error[E1310]
   ￭ command-line exec string
   2 | def f (n : ℕ) : ℕ ≔ match n return _ _ ↦ _ [ zero. ↦ n | suc. k ↦ k ]
     ^ wrong number of arguments for match motive: should be 1

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1311"><summary><code>E1311</code> Wrong_boundary_of_pattern_variable</summary>

This error is reported when a pattern variable in a higher-dimensional
``match`` is given the wrong number of explicit boundary variables in braces.
If any are given, there must be exactly one for each face of the variable's
cube, the last of them, written without braces, being the top face: two in
braces and one without in a one-dimensional match. In an ordinary
zero-dimensional match none may be given. The message says how many are extra
or missing.

Neighboring codes: ``E1306`` if the same constructor is written with boundary
variables in one branch and without them in another, ``E0510`` and ``E0508``
for the choice between ``↦`` and ``⤇``, and ``E1303`` for the number of
arguments of the constructor. For constructors in terms, the corresponding
errors are ``E0507`` and ``E1004``.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} m2 ↦ m0 ]

   ￫ error[E1311]
   ￭ command-line exec string
   2 | def bad (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) : ℕ ≔ match y2 [ zero. ↦ 0 | suc. {m0} m2 ↦ m0 ]
     ^ not enough boundary arguments for higher-dimensional pattern variable (need 1 more)

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E14xx: Comatches</h2>

.. raw:: html

   <details class="error-code" id="E1400"><summary><code>E1400</code> Comatching_at_noncodata</summary>

This error is reported when a comatch ``[ .method ↦ … | … ]`` is checked
against a type that is not a codatatype. Comatches do not synthesize, so they
can only be used where the expected type is defined with ``codata``. A record
type defined with ``sig`` is not a codatatype in this sense: its elements are
written as tuples.

Neighboring codes: ``E1401`` if the expected type is a codatatype with a
nonidentity degeneracy applied. The counterparts for the other checking terms
are ``E0900`` for tuples and ``E0700`` for abstractions.

**Example**

.. code-block:: none

   axiom A : Type
   axiom a : A
   def t : A ≔ [ .head ↦ a ]

   ￫ error[E1400]
   ￭ command-line exec string
   3 | def t : A ≔ [ .head ↦ a ]
     ^ checking comatch against non-codata type A

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1401"><summary><code>E1401</code> Comatching_at_degenerated_codata</summary>

This error is reported when a comatch is checked against a higher-dimensional
instance of a codatatype to which a nonidentity degeneracy, such as ``sym``,
is applied. This arises for codatatypes that are themselves
higher-dimensional, such as a ``Gel`` that is defined with ``codata``.

Neighboring codes: the same restriction is ``E0901`` for tuples and ``E0800``
for field projections. If the expected type is not a codatatype at all, the
error is ``E1400``.

**Example**

Run this example with the ``-parametric`` flag. The type ``T`` is an instance
of ``Gel`` with ``sym`` applied to it.

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ codata [ x .ungel : R x.0 x.1 ]
   axiom A : Type
   axiom R : A → A → Type
   axiom a : A
   axiom r : R a a
   def T ≔ sym (refl Gel (refl A) (refl A) (refl R)) {a} {a} [ .ungel ↦ r ] {a} {a} [ .ungel ↦ r ] (refl a) (refl a)
   def t : T ≔ [ .ungel ↦ refl r ]

   ￫ error[E1401]
   ￭ command-line exec string
   7 | def t : T ≔ [ .ungel ↦ refl r ]
     ^ can't comatch against a codatatype Gel with a nonidentity degeneracy applied

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1402"><summary><code>E1402</code> Missing_method_in_comatch</summary>

This error is reported when a comatch does not define one of the methods of
the codatatype it is checked against. Every method needs a clause, including
each instance of a higher field. The method is marked as failed and checking
continues, so every missing method is reported. A misspelled method name gives
this error together with ``E1403``.

Neighboring codes: ``E1403`` for a clause that the codatatype does not have,
``E1404`` for a repeated clause, and ``E0902`` for a missing field in a tuple.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def Stream : Type ≔ codata [ s .head : ℕ | s .tail : Stream ]
   def zeros : Stream ≔ [ .head ↦ zero. ]

   ￫ error[E1402]
   ￭ command-line exec string
   3 | def zeros : Stream ≔ [ .head ↦ zero. ]
     ^ codata method 'tail' missing in comatch

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1403"><summary><code>E1403</code> Extra_method_in_comatch</summary>

This error is reported when a comatch has a clause for a method that the
codatatype it is checked against does not have. For a higher field, a wrong
dimension suffix has the same effect. The extra clause is reported and
discarded, and checking continues; a misspelled method name usually gives
``E1402`` for the intended method as well. In the message the name is followed
by a dot, which separates it from its dimension suffix.

Neighboring codes: ``E1404`` if the same method has two clauses, and ``E0903``
for an extra field in a tuple.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def Stream : Type ≔ codata [ s .head : ℕ | s .tail : Stream ]
   def zeros : Stream ≔ [ .head ↦ zero. | .tail ↦ zeros | .last ↦ zero. ]

   ￫ error[E1403]
   ￭ command-line exec string
   3 | def zeros : Stream ≔ [ .head ↦ zero. | .tail ↦ zeros | .last ↦ zero. ]
     ^ method 'last.' in comatch doesn't occur in codata type

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1404"><summary><code>E1404</code> Duplicate_method_in_comatch</summary>

This error is reported when the same method has more than one clause in a
comatch. This is detected before typechecking, by comparing the method names
together with their dimension suffixes, so it is reported whatever the
expected type is, and the comatch is not processed any further.

Neighboring codes: ``E0904`` for a repeated field in a tuple, and ``E1502``
for a method declared twice in a ``codata`` definition.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def Stream : Type ≔ codata [ s .head : ℕ | s .tail : Stream ]
   def zeros : Stream ≔ [ .head ↦ zero. | .tail ↦ zeros | .head ↦ zero. ]

   ￫ error[E1404]
   ￭ command-line exec string
   3 | def zeros : Stream ≔ [ .head ↦ zero. | .tail ↦ zeros | .head ↦ zero. ]
     ^ method 'head.' appears more than once in comatch

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1405"><summary><code>E1405</code> Invalid_method_in_comatch</summary>

This code is reserved for a clause of a comatch that does not begin with a
valid method name. The message is ``invalid method in comatch``. In the
current source code this error is not raised anywhere, so users are not
expected to see it: such input is rejected by other errors, usually a parse
error ``E0200``.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E15xx: Canonical types</h2>

.. raw:: html

   <details class="error-code" id="E1500"><summary><code>E1500</code> Universe_expected</summary>

This error is reported when a term that must be a type is given a type that is
not a universe. This happens when a ``data``, ``codata`` or ``sig`` definition
is checked against something that is not a universe (``Type``, or a
higher-dimensional instance of it such as ``Id Type A B``) or, for an indexed
datatype, a function type ending in one. It also happens when the type
ascribed to a ``let only`` variable does not itself have a universe as its
type. The message says which of these is the case; a ``sig`` written with self
variables is called a codatatype there.

Neighboring codes: writing something that is not a type where a type is
expected elsewhere gives an ordinary type mismatch such as ``E0401``.

**Example**

.. code-block:: none

   axiom A : Type
   def D : A ≔ data [ c. ]

   ￫ error[E1500]
   ￭ command-line exec string
   2 | def D : A ≔ data [ c. ]
     ^ checking datatype at non-universe A

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1501"><summary><code>E1501</code> Duplicate_field_in_record</summary>

This error is reported when a record type declares the same field name twice.
Every field of a ``sig`` must have a distinct name. This is detected before
typechecking.

Neighboring codes: ``E0904`` if the same field is given twice in a tuple,
``E1502`` for a method declared twice in a codatatype, and ``E1503`` for a
constructor declared twice in a datatype.

**Example**

.. code-block:: none

   axiom A : Type
   axiom B : Type
   def S : Type ≔ sig (x y : A, z y : B)

   ￫ error[E1501]
   ￭ command-line exec string
   3 | def S : Type ≔ sig (x y : A, z y : B)
     ^ duplicate field in record type: y

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1502"><summary><code>E1502</code> Duplicate_method_in_codata</summary>

This error is reported when a codatatype declares the same method twice, with
the same name and the same dimension. Every method of a ``codata`` must be
distinct.

Neighboring codes: the same name declared once as an ordinary method and once
as a higher-dimensional one is ``E1507``. A method defined twice in a comatch
is ``E1404``, and a field declared twice in a record type is ``E1501``.

**Example**

.. code-block:: none

   axiom A : Type
   def C : Type ≔ codata [ x .f : A | x .f : A ]

   ￫ error[E1502]
   ￭ command-line exec string
   2 | def C : Type ≔ codata [ x .f : A | x .f : A ]
     ^ duplicate method in codatatype: f

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1503"><summary><code>E1503</code> Duplicate_constructor_in_data</summary>

This error is reported when a datatype declares the same constructor name
twice. Only the names are compared, so different lists of arguments do not
help. The same constructor name may be used in different datatypes, but within
one datatype it must be unique.

Neighboring codes: ``E1302`` for two branches for the same constructor in a
``match``, ``E1501`` for a repeated field in a record type, and ``E1502`` for
a repeated method in a codatatype.

**Example**

.. code-block:: none

   axiom A : Type
   def D : Type ≔ data [ c. | c. (_ : A) ]

   ￫ error[E1503]
   ￭ command-line exec string
   2 | def D : Type ≔ data [ c. | c. (_ : A) ]
     ^ duplicate constructor in datatype: c

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1504"><summary><code>E1504</code> Wrong_boundary_of_record</summary>

This error is reported when a record type is defined with the wrong number of
boundary variables. Their number must equal the number of boundary components
of the type being defined: two for a type in ``Id Type A B``, and none for an
ordinary record type. The message says how many are extra or missing.

In the deprecated ``sig x y ↦ (…)`` syntax, these are the variables named
before ``↦``; since that syntax is deprecated, the warning ``E0101`` then
precedes this error. A plain ``sig (…)`` without ``↦`` names no boundary
variables, so it gives this error, without the warning, when it is checked
against a higher-dimensional universe such as ``Id Type A B``; a
higher-dimensional record type has to be written with a self variable instead.

Neighboring codes: ``E1500`` if the type that the definition is checked
against is not a universe.

**Example**

Run this example with the ``-parametric`` flag.

.. code-block:: none

   def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b c ↦ (ungel : R a b)

   ￫ warning[E0101]
   ￭ command-line exec string
   1 | def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b c ↦ (ungel : R a b)
     ^ deprecated: 'sig … ↦' for higher records: use self variables

   ￫ error[E1504]
   ￭ command-line exec string
   1 | def Gel (A B : Type) (R : A → B → Type) : Id Type A B ≔ sig a b c ↦ (ungel : R a b)
     ^ too many variables in boundary of higher-dimensional record (1 extra)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1505"><summary><code>E1505</code> Invalid_constructor_type</summary>

This error is reported when the output type written for a constructor is not a
valid instance of the datatype being defined. After the colon, the type of a
constructor must end in the datatype itself, applied to the same parameters
and to the right number of indices; the message says which of these conditions
fails. Only that constructor fails, and the other constructors are still
checked.

Neighboring codes: ``E1506`` if a constructor of an indexed datatype has no
output type at all. Simple mistakes in the number of indices are usually
reported earlier, as ``E0401`` or ``E0505``.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def D : Type ≔ data [ c. : ℕ ]

   ￫ error[E1505]
   ￭ command-line exec string
   2 | def D : Type ≔ data [ c. : ℕ ]
     ^ invalid output type for constructor c: head must be current datatype

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1506"><summary><code>E1506</code> Missing_constructor_type</summary>

This error is reported when a constructor of an indexed datatype is declared
without an output type. When a datatype has indices, every constructor must be
given an explicit type after a colon, since that type determines the values of
the indices. Parameters, written before the colon of the definition, are not
indices and do not require this. The error is reported once for each such
constructor, and checking continues.

Neighboring codes: ``E1505`` if an output type is given but is not a valid
instance of the datatype being defined.

**Example**

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   def D : ℕ → Type ≔ data [ c. ]

   ￫ error[E1506]
   ￭ command-line exec string
   2 | def D : ℕ → Type ≔ data [ c. ]
     ^ missing type for constructor c of indexed datatype

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1507"><summary><code>E1507</code> Lower_and_higher_methods_in_codata</summary>

This error is reported when a codatatype declares an ordinary method and a
higher-dimensional method with the same name, such as ``.f`` and ``.f.e``. A
name cannot be used both for a zero-dimensional and for a higher-dimensional
method. The later declaration is ignored, and checking continues.

Neighboring codes: ``E1502`` if the two declarations have the same name and
the same dimension.

**Example**

.. code-block:: none

   axiom A : Type

   def foo : Type ≔ codata [
   | x .f : A
   | x .f.e : A → A ]

   ￫ error[E1507]
   ￭ command-line exec string
   3 | def foo : Type ≔ codata [
   4 | | x .f : A
   5 | | x .f.e : A → A ]
     ^ codatatype has both lower and higher methods named 'f'

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1508"><summary><code>E1508</code> Invalid_self_variable_type</summary>

This error is reported when the type ascribed to the self variable of a field,
as in ``(x : T) .f``, is not the record type or codatatype that is being
defined. If a type is written there, it must be that type itself, applied to
the same parameters; the message names the field and says what differs.

Neighboring codes: ``E1505`` is the analogous error for the output type of a
constructor. A modal annotation on the self variable that is not allowed is
``E1711``.

**Examples**

.. code-block:: none

   axiom A : Type
   def S : Type ≔ sig ( (x : A) .f : A )

   ￫ error[E1508]
   ￭ command-line exec string
   2 | def S : Type ≔ sig ( (x : A) .f : A )
     ^ invalid self variable type for field f: head must be current record

Run this example with the ``-coreflection`` flag.

.. code-block:: none

   def □ (A :□| Type) : Disc ≔ sig ((x :△| Disc) .□ : A)

   ￫ error[E1508]
   ￭ command-line exec string
   1 | def □ (A :□| Type) : Disc ≔ sig ((x :△| Disc) .□ : A)
     ^ invalid self variable type for field □: head must be current record

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E16xx: Tactics</h2>

.. raw:: html

   <details class="error-code" id="E1600"><summary><code>E1600</code> Choice_mismatch</summary>

This error is reported when an internal multiple-choice term, which offers
several alternative elaborations selected by the shape of the type, has no
alternative that fits the type it is checked against. The message has the form
``multi-choice term doesn't match type …``. Narya's parser never produces such
terms, so users are not expected to see this error.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1601"><summary><code>E1601</code> Calc_error</summary>

This error is reported when a step of a ``calc`` chain written without a
``by`` clause relates two terms that are not definitionally equal. A step ``=
z by p`` is justified by the reason ``p``; a step with no ``by`` clause is
accepted only if its two sides are already definitionally equal. The message
is ``error in calc: unequal term``, and the location is the new term of the
step. See :ref:`Equational reasoning`.

Neighboring codes: a reason of the wrong type gives ordinary type errors such
as ``E0401``. Outside HOTT, for instance with ``-parametric``, ``calc`` gives
``E0100``.

**Example**

.. code-block:: none

   axiom A : Type
   axiom x : A
   axiom y : A
   axiom z : A
   axiom p : Id A x y
   def bad : Id A x z ≔ calc x = y by p = z ∎

   ￫ error[E1601]
   ￭ command-line exec string
   6 | def bad : Id A x z ≔ calc x = y by p = z ∎
     ^ error in calc: unequal term

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1602"><summary><code>E1602</code> No_implicit_goal_arg</summary>

This error is reported when an internal "implicit application" term, in which
the first argument of a function is taken from the type being checked against,
finds no suitable argument in that type. The message has the form ``can't take
an implicit argument for … from type …``. Narya's parser never produces such
terms, so users are not expected to see this error.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E17xx: Modal type theory</h2>

.. raw:: html

   <details class="error-code" id="E1700"><summary><code>E1700</code> Mode_mismatch</summary>

This error is reported when something that belongs to one mode is used where
another mode is required. Typical causes are a constant or a universe of one
mode inside a term of another mode, or a modality or 2-cell whose source or
target mode does not fit the context. The message gives the operation and the
two modes. When the same mismatch is found by an internal consistency check,
it is reported as a bug instead.

Neighboring codes: ``E1704`` and ``E1706`` if the name of a modality or 2-cell
is unknown, ``E1701`` if the modes fit but the modalities differ, and
``E1703`` if the mode of a command cannot be determined.

**Example**

Run this example with the ``-adjunction`` flag, which has the two modes
``Type`` and ``Disc``.

.. code-block:: none

   axiom A : Disc
   def B : Type ≔ A

   ￫ error[E1700]
   ￭ command-line exec string
   2 | def B : Type ≔ A
     ^ mode mismatch in synthesizing constant (Disc ≠ Type)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1701"><summary><code>E1701</code> Modality_mismatch</summary>

This error is reported when a modality annotation written by the user differs
from the modality that is required at that place. For example the variable of
an abstraction is annotated with a modality other than that of the function
type it is checked against, or the window modality written in a ``match`` on a
variable differs from the annotation of that variable. The message shows the
two modalities; ``id`` is the identity modality, that is, no annotation. When
the same mismatch is found by an internal consistency check, it is reported as
a bug instead.

Neighboring codes: ``E1700`` if the modes do not fit, ``E1704`` if the
modality name is unknown, and ``E1705`` if a variable is used behind a lock
without a key.

**Example**

Run this example with the ``-coreflector`` flag.

.. code-block:: none

   axiom A : Type
   def B : Type ≔ data [ t. ]
   def f : (x : A) → B ≔ (x :♭| A) ↦ t.

   ￫ error[E1701]
   ￭ command-line exec string
   3 | def f : (x : A) → B ≔ (x :♭| A) ↦ t.
     ^ modality mismatch in checking ascribed lambda (♭ ≠ id)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1702"><summary><code>E1702</code> Modalcell_mismatch</summary>

This code is reserved for two modal 2-cells that are expected to be equal but
differ. The message has the form ``modal cell mismatch in … (α ≠ β)``. In the
current source code this error is not raised anywhere, so users are not
expected to see it.

Neighboring codes: a mismatch of modes is ``E1700`` and a mismatch of
modalities is ``E1701``. Mistakes with keys are reported as ``E1706`` for an
unknown 2-cell, ``E1707`` for a key that does not fit the locks of the
context, and ``E1705`` for a missing key.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1703"><summary><code>E1703</code> Non_mode_synthesizing</summary>

This error is reported when, in a mode theory with more than one mode, Narya
cannot determine the mode of a command. The mode of an ``axiom``, ``def``,
``echo`` or ``synth`` command is deduced from its parameters and from its type
or term, for instance from a universe or a constant that occurs there; if
nothing determines a mode, as when the type of an ``axiom`` or ``def`` is a
bare hole, or in ``echo (? : ?)``, this error is reported. The last word of
the message names the command (``echo`` is also shown for ``synth``). An
explicit type such as ``: Type`` determines the mode.

Neighboring codes: ``E0400`` is about a term whose type cannot be synthesized,
rather than its mode; it is what ``echo ?`` reports.

**Example**

Run this example with the ``-adjunction`` flag, which has the two modes
``Type`` and ``Disc``.

.. code-block:: none

   axiom A : ?

   ￫ error[E1703]
   ￮ cannot synthesize a mode: axiom

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1704"><summary><code>E1704</code> Unknown_modality</summary>

This error is reported when a modality name is used that does not exist in the
selected mode theory. This can happen wherever a modality is written: in an
annotation ``(x :μ| A)``, in a ``lock`` clause of ``let only``, as the window
modality of a ``match``, or in the annotation of a field or of a field
projection. With the default names of the built-in mode theories, modality
names are single characters and composites are written without separators, so
the message shows only the character that is not found. Typical causes are a
typo, the wrong mode-theory flag, or a renaming with ``-modalities``.

Neighboring codes: ``E1700`` if the name exists but its source or target mode
does not fit, ``E1701`` if it differs from the modality required there, and
``E1706`` for an unknown 2-cell.

**Example**

Run this example with the ``-coreflector`` flag, whose only modality is ``♭``.

.. code-block:: none

   axiom A : Type
   axiom f : (x :♮| A) → A

   ￫ error[E1704]
   ￭ command-line exec string
   2 | axiom f : (x :♮| A) → A
     ^ unknown modality ♮

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1705"><summary><code>E1705</code> Missing_key</summary>

This error is reported when a variable is used at a place where the locks in
the context do not permit it directly. A variable annotated with a modality
``μ`` can be used behind locks ``ν`` only by way of a 2-cell, a key, from
``μ`` to ``ν``. Narya inserts the key automatically when there is exactly one;
otherwise it reports this error, either because no such 2-cell exists or
because the key must be written explicitly with ``#``. See :ref:`Keys`.

Neighboring codes: ``E1707`` if a key is written but does not fit the locks of
the context, ``E0306`` if the variable is hidden altogether, and ``E0304`` for
a nonparametric constant in a locked context. A window modality that differs
from the annotation of the variable is ``E1701``.

**Examples**

Run this example with the ``-coreflector`` flag. The argument of ``f`` is
checked behind a ``♭`` lock, and ``x`` has no annotation.

.. code-block:: none

   axiom A : Type
   axiom f : (y :♭| A) → A
   def g (x : A) : A ≔ f x

   ￫ error[E1705]
   ￭ command-line exec string
   3 | def g (x : A) : A ≔ f x
     ^ use of id variable behind ♭ lock requires a key

Run this example with the ``-dtt`` flag, where an external degeneracy locks
the context:

.. code-block:: none

   def foo (X:Type) : Type^^(d) X := X^^(d)

   ￫ error[E1705]
   ￭ command-line exec string
   1 | def foo (X:Type) : Type^^(d) X := X^^(d)
     ^ use of id variable behind △□ lock requires a key

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1706"><summary><code>E1706</code> Unknown_modalcell</summary>

This error is reported when a 2-cell name used as a key, with ``#`` or in a
``key`` clause of ``let only``, does not exist in the selected mode theory.
The message may show only a part of the name that is written, or even a single
character of it. Typical causes are a typo, the wrong mode-theory flag, or a
renaming with ``-modalcells``.

Neighboring codes: ``E1700`` if the 2-cell exists but its modes do not fit the
context, ``E1707`` if it does not fit the locks of the context, and ``E1704``
for an unknown modality name.

**Example**

Run this example with the ``-coreflector`` flag.

.. code-block:: none

   axiom A : Type
   def f (x :♭| A) : A ≔ x #η

   ￫ error[E1706]
   ￭ command-line exec string
   2 | def f (x :♭| A) : A ≔ x #η
     ^ unknown modal cell η

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1707"><summary><code>E1707</code> Key_mismatch</summary>

This error is reported when a key is applied where the locks in the context do
not end with the target modality of the key. A key ``#α`` for a 2-cell ``α : μ
⇒ ν`` can only be used in a context whose locks end in ``ν``; those locks are
replaced by ``μ`` while the term it is applied to is checked. The same
condition applies to an ``and key α`` clause of ``let only``. The message
shows the target of the key, the key itself and the locks of the context. See
:ref:`Keys`.

Neighboring codes: ``E1706`` if the 2-cell is unknown, ``E1700`` if its modes
do not fit the context, and ``E1705`` if a key is needed but not written. A
variable that becomes inaccessible because a key replaces locks gives
``E0306``, and the corresponding mismatch for a ``lock`` clause is ``E1716``.

**Example**

Run this example with the ``-adjunction`` flag. The key ``η`` has target
``□△``, but the body is checked in a context with no locks, so there is
nothing for the key to replace.

.. code-block:: none

   axiom A : Disc
   def f (x : A) : A ≔ x #η

   ￫ error[E1707]
   ￭ command-line exec string
   2 | def f (x : A) : A ≔ x #η
     ^ vertical target □△ of key cell(c0c1) doesn't match any suffix of context locks id

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1708"><summary><code>E1708</code> Nonparametric_mode_degeneracy</summary>

This error is reported when a degeneracy that adds dimensions, such as
``refl`` or ``Id``, is applied at a mode that is nonparametric. In the
discrete mode theories some modes are declared nonparametric, and such
operations are not available on terms at those modes. See :ref:`Modal
parametric discreteness`.

Neighboring codes: ``E0601`` and ``E0602`` concern the dimension of a term
rather than its mode. A nonparametric constant used in a locked context is
``E0304``.

**Example**

Run this example with the flags ``-discrete-functor -parametric``, where the
mode ``DomType`` is discrete.

.. code-block:: none

   axiom A : DomType
   axiom a : A
   synth refl a

   ￫ error[E1708]
   ￭ command-line exec string
   3 | synth refl a
     ^ degeneracy refl is not allowed at mode DomType, which is nonparametric

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1709"><summary><code>E1709</code> Intangible_modality</summary>

This error is reported when a modality that is not tangible is used to
annotate the domain of a function type, a parameter or constructor argument,
or a ``let`` binding. Only tangible modalities may annotate variables. In most
mode theories every modality is tangible; some modalities of the discrete mode
theories, such as ``♯`` in ``-discrete-spatial``, are not, and can only be
defined negatively, as a codatatype with a modal field.

Neighboring codes: for the annotation of a field the required property is to
be sinister, ``E1711``, and for the window of a ``match`` it is ``E1715``. An
unknown modality name is ``E1704``.

**Example**

Run this example with the flags ``-discrete-spatial -parametric``.

.. code-block:: none

   axiom A : Type
   axiom f : (x :♯| A) → A

   ￫ error[E1709]
   ￭ command-line exec string
   2 | axiom f : (x :♯| A) → A
     ^ modality ♯ is not tangible

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1710"><summary><code>E1710</code> Invalid_mode_theory</summary>

This error is reported when the implementation of the selected mode theory
returns data that violates an invariant on which Narya relies. Seeing it
indicates a bug in Narya, which should be reported to the developers together
with the flags in use.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1711"><summary><code>E1711</code> Modality_not_sinister</summary>

This error is reported when the self variable of a field in a record type or
codatatype is annotated with a modality that is not sinister. A modal field is
declared as ``(x :μ| _) .f : T``, and this requires ``μ`` to be a left
adjoint, that is, to have a right adjoint in the mode theory. For example,
with ``-spatial`` the modality ``♭`` is sinister but ``♯`` is not. See
:ref:`Modal records and codata`.

Neighboring codes: ``E1704`` if the modality name is unknown and ``E1700`` if
its mode does not fit. The property required of a variable annotation is
tangibility, ``E1709``, and projecting a modal field with the wrong annotation
is ``E1712``.

**Example**

Run this example with the ``-spatial`` flag.

.. code-block:: none

   def Bad : Type ≔ codata [ | (x :♯| _) .f : Type ]

   ￫ error[E1711]
   ￭ command-line exec string
   1 | def Bad : Type ≔ codata [ | (x :♯| _) .f : Type ]
     ^ modal field annotation ♯ is not sinister

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1712"><summary><code>E1712</code> Wrong_locking_modality</summary>

This error is reported when a field is projected with the wrong locking
annotation. A modal field declared as ``(x :μ| _) .f`` must be projected as
``(t :μ| _) .f`` with the same modality ``μ``, because Narya cannot infer it
from the field name, while an ordinary field must be projected without any
annotation. The message says which modality is expected and which is given.

Neighboring codes: ``E0800`` if the type has no field of that name, and
``E1713`` if the annotation is right but the field does not exist at that
dimension. Once the annotation is written, the projected term is checked in a
locked context, where ``E1705`` can arise for its variables.

**Example**

Run this example with the ``-spatial`` flag.

.. code-block:: none

   def N : Type ≔ data [ zero. | suc. (_ : N) ]
   def C : Type ≔ codata [ (x :♭| _) .fld : N ]
   axiom c : C
   echo c .fld

   ￫ error[E1712]
   ￭ command-line exec string
   4 | echo c .fld
     ^ field fld is modal with left adjoint ♭, so projecting it requires a locking annotation such as (_ : ♭ | _) .fld

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1713"><summary><code>E1713</code> Modal_field_filtered_away</summary>

This error is reported when a modal field is projected from a
higher-dimensional element at a dimension where the field does not exist. In a
discrete mode theory, a field whose modality is discrete vanishes from the
higher-dimensional versions of its record type or codatatype, so it cannot be
projected from, for instance, ``refl c``.

Neighboring codes: ``E1714`` if such a field is given a value in a tuple or
comatch, ``E1712`` if the locking annotation is wrong, and ``E0800`` if the
type has no field of that name at all.

**Example**

Run this example with the flags ``-discrete-spatial -parametric``, where ``♭``
is discrete.

.. code-block:: none

   def N : Type ≔ data [ zero. | suc. (_ : N) ]
   def C : Type ≔ codata [ (x :♭| _) .fld : N ]
   axiom c : C
   echo (refl c :♭| _) .fld

   ￫ error[E1713]
   ￭ command-line exec string
   4 | echo (refl c :♭| _) .fld
     ^ field fld does not exist at this dimension: its modality ♭ is discrete there

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1714"><summary><code>E1714</code> Extra_filtered_field_in_tuple</summary>

This error is reported when a tuple or comatch for a higher-dimensional
element supplies a modal field that does not exist at that dimension. In a
discrete mode theory, a field whose modality is discrete vanishes from the
higher-dimensional versions of its type, so it must be left out there. The
field is discarded and checking continues.

Neighboring codes: ``E1713`` if such a field is projected. A field or method
that the type does not have at any dimension is ``E0903`` in a tuple and
``E1403`` in a comatch.

**Example**

Run this example with the flags ``-discrete-spatial -parametric``, where ``♭``
is discrete.

.. code-block:: none

   def N : Type ≔ data [ zero. | suc. (_ : N) ]
   def C : Type ≔ codata [ (x :♭| _) .fld : N ]
   axiom c : C
   def bad : Id C c c ≔ [ .fld ↦ refl (suc. zero.) ]

   ￫ error[E1714]
   ￭ command-line exec string
   4 | def bad : Id C c c ≔ [ .fld ↦ refl (suc. zero.) ]
     ^ field fld must be omitted at this dimension: its modality ♭ is discrete there

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1715"><summary><code>E1715</code> Nontransparent_window_modality</summary>

This error is reported when the window modality of a ``match`` is not
permitted for the datatype that is matched on. The identity window is always
allowed, and any datatype can be matched through a pellucid window; a
transparent window is allowed only for non-recursive datatypes, and a
translucent one only for non-recursive datatypes with exactly one constructor.
The message says which property the modality would need. See :ref:`Windowed
matches`.

Neighboring codes: ``E1701`` if the window that is written differs from the
annotation of the variable. If an unsuitable modality prevents the automatic
refutation of an omitted branch, the error is ``E1300``, preceded by the hint
``E1102`` when hints are displayed (in interactive mode, or with ``-v``).

**Example**

Run this example with the ``-functor`` flag, where ``○`` is only translucent
and ``B`` has two constructors.

.. code-block:: none

   def ○ (A :○| DomType) : CodType ≔ data [ ○. (_ :○| A) ]
   def B : DomType ≔ data [ t. | f. ]
   def bad (u : ○ B) : ○ B ≔ match u [ ○. w ↦ match (w :○| _) [ t. ↦ u | f. ↦ u ] ]

   ￫ error[E1715]
   ￭ command-line exec string
   3 | def bad (u : ○ B) : ○ B ≔ match u [ ○. w ↦ match (w :○| _) [ t. ↦ u | f. ↦ u ] ]
     ^ window modality ○ must be pellucid or transparent

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E1716"><summary><code>E1716</code> Letonly_lock_mismatch</summary>

This error is reported when a ``lock`` clause in a ``let only`` names a
modality that does not match the locks of the surrounding context. The clause
``and lock μ`` is allowed only when the locks of the context end in ``μ``, for
example inside the argument of a ``μ``-modal constructor; those locks are
stripped while the terms bound to its left are checked. The message shows the
lock and the locks of the context. See :ref:`Modal let-only`.

Neighboring codes: ``E1707`` is the same mismatch for a ``key`` clause. An
unknown modality name is ``E1704``, and using a variable that is hidden by the
stripped lock is ``E0306``.

**Example**

Run this example with the ``-coreflector`` flag. The body is checked in a
context with no locks.

.. code-block:: none

   def k (A : Type) : Type ≔ let only B : Type ≔ A and lock ♭ in B

   ￫ error[E1716]
   ￭ command-line exec string
   1 | def k (A : Type) : Type ≔ let only B : Type ≔ A and lock ♭ in B
     ^ let-only lock ♭ doesn't match any suffix of context locks id

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E20xx: Commands</h2>

.. raw:: html

   <details class="error-code" id="E2000"><summary><code>E2000</code> Too_many_commands</summary>

In interactive mode and in ProofGeneral mode, each input must consist of
exactly one command. This error is reported when a single input contains more
than one command; none of them is executed. The message is ``too many
commands: enter one at a time``. Files and ``-e`` strings may contain any
number of commands, so the error cannot arise there.

Neighboring codes: ``E2001`` is the opposite restriction, a command that is
only allowed interactively appearing in a file or an ``-e`` string.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2001"><summary><code>E2001</code> Forbidden_interactive_command</summary>

The commands ``solve``, ``split``, ``show`` and ``undo`` are only allowed in
interactive mode, including ProofGeneral mode. This error is reported when one
of them appears in a file or in an ``-e`` string; the message names the
command.

Neighboring codes: in interactive mode, an ``undo`` of more commands than can
be undone is ``E2500``. The commands ``solve`` and ``split`` look up their
hole while they are parsed, before this restriction is checked, so in a file
or an ``-e`` string they do not reach this error: if there is no open hole
with that number they report ``E3001``, and if there is one they currently
fail with the ``E0000`` anomaly ``timeless hole``, which is a bug in Narya.

**Example**

.. code-block:: none

   undo 1

   ￫ error[E2001]
   ￮ command 'undo' only allowed in interactive mode

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2002"><summary><code>E2002</code> No_holes_allowed</summary>

This error is reported when a hole ``?`` is found in a place where holes are
not permitted. Holes may appear in files given on the command line, in ``-e``
strings and in interactive input, but not in a file that is loaded with
``import``. The location is that of the hole.

Neighboring codes: ``E3002`` if a command-line input ends while it still
contains open holes.

**Example**

.. code-block:: none

   $ echo 'def A : Type ≔ ?' > lib.ny
   $ narya -e 'import "lib"'

   ￫ error[E2002]
   ￭ …/lib.ny
   1 | def A : Type ≔ ?
     ^ imported file '…/lib.ny' cannot contain holes

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2003"><summary><code>E2003</code> Invalid_instant</summary>

This error is reported when the parser is asked to go back to a point in the
command history, an "instant", that is not available: either it is later than
the current one, or the input is not interactive at all, since files and
``-e`` strings have no instants. The message has the form ``invalid instant:
…``.

There are two ways to reach it. Commands that refer to a hole (``solve``,
``split``, ``echo in``, ``synth in`` and ``about in``) are parsed with the names and notations that were
in scope when the hole was created. If the instant of the hole is not valid,
the error is reported as a bug in Narya, which should be reported to the
developers.

The other way is the ``fmt n ≔ …`` command, which parses a command with the
names and notations of the instant numbered ``n`` so that it can be
reformatted. It is meant to be issued by editor integrations rather than
typed by hand, and an invalid ``n`` there is reported as an ordinary error.

**Example**

.. code-block:: none

   fmt 5 ≔ axiom A : Type

   ￫ error[E2003]
   ￮ invalid instant: 5

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2004"><summary><code>E2004</code> Break</summary>

This error is reported when the command that is being executed in ProofGeneral
mode is interrupted by the user, with Ctrl-C. The command is abandoned, and
Narya waits for the next one. The message is ``user interrupt``. This is not a
mistake in the code but the confirmation that the interrupt was carried out.

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2005"><summary><code>E2005</code> Invalid_flags</summary>

This error is reported when the command-line flags are inconsistent: an arity
other than 2 is given without ``-parametric``. By default Narya runs higher
observational type theory, which requires arity 2. The error depends only on
the flags, shows no source location, and nothing is executed.

Neighboring codes: other invalid combinations of flags, such as ``-external``
without ``-parametric``, are rejected with a plain message that has no error
code. An arity outside the supported range is ``E0100``.

**Example**

Run this example with the flags ``-arity 1``.

.. code-block:: none

   axiom A : Type

   ￫ error[E2005]
   ￮ invalid combination of command-line flags

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E21xx: Defining constants</h2>

.. raw:: html

   <details class="error-code" id="E2100"><summary><code>E2100</code> Redefining_constant</summary>

This warning is reported when a constant is defined or assumed with a name
that already has a definition that will be exported from the current scope:
typically one made earlier in the same file or, inside a section, earlier in
that section, but also one brought in with ``export``. A name defined outside
the currently open section, or brought in with ``import``, does not give the
warning. Despite its ``E`` code this is a warning and does not stop
processing: the new definition shadows the old one. When the location of the
earlier definition is known, it is marked as well. The same warning is given
for a ``notation`` command whose pattern is that of an existing notation.

Neighboring codes: ``E2209`` if a second notation is declared for the same
constant or constructor, and ``E2101`` if the name itself is not valid.

**Example**

.. code-block:: none

   axiom A : Type
   axiom A : Type

   ￫ warning[E2100]
   ￭ command-line exec string
   1 | axiom A : Type
     ^ previous definition
   2 | axiom A : Type
     ^ redefining constant: A

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2101"><summary><code>E2101</code> Invalid_constant_name</summary>

This error is reported when the name given to ``def`` or ``axiom`` cannot be
used for a constant. Either one of its components is not a valid identifier,
for instance because it begins with an underscore or consists only of digits,
or the name is reserved for a degeneracy (by default ``refl``, ``Id``, ``ap``
and ``sym``) or for a mode (such as ``Type``). In the last two cases the
message says which.

Neighboring codes: a valid name that is already in use gives the warning
``E2100``.

**Examples**

.. code-block:: none

   axiom Type : Type

   ￫ error[E2101]
   ￮ invalid constant name: Type (that's a mode name)

.. code-block:: none

   axiom refl : Type

   ￫ error[E2101]
   ￮ invalid constant name: refl (that's a degeneracy name)

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E22xx: Notation definitions</h2>

.. raw:: html

   <details class="error-code" id="E2200"><summary><code>E2200</code> Invalid_tightness</summary>

This error is reported when the tightness given in parentheses in a
``notation`` command is not valid. A tightness must be a finite dyadic
rational number, that is, one whose denominator is a power of 2, such as
``0``, ``1.5`` or ``-2``; so ``0.1`` is not allowed.

Neighboring codes: ``E2203`` if a valid tightness is given or omitted where
the pattern does not allow it.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A->A
   notation(0.1) x "&" y := f x y

   ￫ error[E2200]
   ￭ command-line exec string
   3 | notation(0.1) x "&" y := f x y
     ^ invalid tightness: 0.1

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2201"><summary><code>E2201</code> Invalid_notation_symbol</summary>

This error is reported when a quoted symbol in the pattern of a ``notation``
command cannot be used as a notation symbol. A symbol must be a single token:
an operator, an identifier without dots, or one of a few special tokens.
Parentheses, strings that consist of several tokens and the empty string are
not allowed.

Neighboring codes: ``E2202`` if the symbols are valid but the pattern as a
whole is malformed, and ``E0202`` if a variable of the pattern is not a valid
name.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A->A
   notation(0) x "&x" y := f x y

   ￫ error[E2201]
   ￮ invalid notation symbol: &x

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2202"><summary><code>E2202</code> Invalid_notation_pattern</summary>

This error is reported when the pattern of a ``notation`` command is
malformed: for instance it contains no symbols, has two variables with no
symbol between them, or uses an ellipsis ``…`` in a way that contradicts the
shape of the notation. The message gives the reason. The same code is used
when a built-in notation that has no meaning as a pattern is used in a pattern
of a ``match``.

Neighboring codes: ``E2201`` if a single symbol is not valid, and ``E2203`` if
the tightness does not agree with the pattern. A pattern that is entirely
empty is a parse error ``E0200``.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A
   notation(0) x := f x

   ￫ error[E2202]
   ￮ invalid notation pattern: has no symbols

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2203"><summary><code>E2203</code> Fixity_mismatch</summary>

This error is reported when the presence or absence of a tightness in a
``notation`` command does not agree with its pattern. A tightness must be
given for infix, prefix and postfix notations, and omitted for outfix
notations, which begin and end with a symbol. A pattern that consists of a
single symbol is accepted with or without a tightness.

Neighboring codes: ``E2200`` if a tightness is given but its value is not
valid, and ``E2202`` if the pattern itself is malformed.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A->A
   notation x "&" y "#" := f x y

   ￫ error[E2203]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2204"><summary><code>E2204</code> Duplicate_notation_variable</summary>

This error is reported when the same variable occurs more than once in the
pattern of a ``notation`` command. Each variable of the pattern must have a
distinct name.

Neighboring codes: depending on how often that variable occurs on the
right-hand side, the same mistake can be reported as ``E2206`` or ``E2207``
instead. A variable on the right-hand side that is not in the pattern is
``E2208``.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A->A
   notation(0) x "&" y "#" x := f x y

   ￫ error[E2204]
   ￮ duplicate notation variable: 'x'

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2205"><summary><code>E2205</code> Invalid_notation_head</summary>

The right-hand side of a ``notation`` command must be a constant or a
constructor applied to the pattern variables. This error is reported when the
head is a name that is not a constant in scope. A constructor is not looked
up, since it is not tied to a particular datatype.

Neighboring codes: an unbound name inside an ordinary term is ``E0300``. A
right-hand side that begins with a parenthesized expression is a parse error
``E0200``.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A->A
   notation(0) x "&" y := Type x y

   ￫ error[E2205]
   ￮ invalid notation head: Type

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2206"><summary><code>E2206</code> Unused_notation_variable</summary>

This error is reported when a variable of the pattern in a ``notation``
command does not appear on the right-hand side. The right-hand side is a
constant or constructor applied to the pattern variables, and each pattern
variable must be used there exactly once, so that the notation can be both
parsed and printed.

Neighboring codes: ``E2207`` if a pattern variable is used more than once on
the right-hand side, ``E2204`` if it occurs twice in the pattern, and
``E2208`` if the right-hand side contains a variable that is not in the
pattern.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A->A
   notation(0) x "&" y "#" z := f x y

   ￫ error[E2206]
   ￮ unused notation variable: 'z'

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2207"><summary><code>E2207</code> Notation_variable_used_twice</summary>

This error is reported when a variable of the pattern in a ``notation``
command appears more than once on the right-hand side. Each pattern variable
must be used exactly once as an argument of the head, so that a term printed
with the notation has one place for each argument. A typical cause is a head
that takes more arguments than the pattern has variables.

Neighboring codes: ``E2206`` if a pattern variable is not used at all,
``E2204`` if the repetition is in the pattern itself, and ``E2208`` for a
variable that is not in the pattern.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A->A
   notation(0) x "/" := f x x

   ￫ error[E2207]
   ￮ notation variable 'x' used twice

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2208"><summary><code>E2208</code> Unbound_variable_in_notation</summary>

This error is reported when the right-hand side of a ``notation`` command uses
a variable that does not occur in the pattern. The names on the right-hand
side are not terms: each of them must be a pattern variable, so a notation
cannot fix some of the arguments of its head. The message lists all such
names.

Neighboring codes: ``E2206`` and ``E2207`` if a pattern variable is used zero
times or more than once, and ``E2204`` if it occurs twice in the pattern. An
unbound name inside an ordinary term is ``E0300``.

**Example**

.. code-block:: none

   axiom A:Type
   axiom f:A->A->A
   notation(0) x "/" := f x y

   ￫ error[E2208]
   ￮ unbound variable(s) in notation definition: y

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2209"><summary><code>E2209</code> Head_already_has_notation</summary>

This warning is reported when a ``notation`` command declares a notation for a
constant or constructor that already has one. For a constructor, only
notations with the same number of arguments count. Despite its ``E`` code this
is a warning and does not stop processing. Both notations can be used for
parsing; as the message says, the new one replaces the old one for printing.

Neighboring codes: ``E2100`` if the new notation has the same pattern as an
existing one. When both the pattern and the head are the same, both warnings
are given.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A → A
   notation(1) x "+" y ≔ f x y
   notation(1) x "*" y ≔ f x y

   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E23xx: Imports and files</h2>

.. raw:: html

   <details class="error-code" id="E2300"><summary><code>E2300</code> Circular_import</summary>

This error is reported when a file imports itself, directly or through a chain
of other files. The message lists the chain of imports that leads back to the
file. Importing a file that has already been loaded, or the same file from two
different files, is not an error.

**Example**

.. code-block:: none

   $ echo 'import "bar"' > foo.ny
   $ echo 'import "foo"' > bar.ny
   $ narya foo.ny

   ￫ error[E2300]
   ￮ circular imports:
     …/foo.ny
       imports …/bar.ny
       imports …/foo.ny

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2302"><summary><code>E2302</code> Invalid_filename</summary>

This error is reported when a file given to Narya on the command line does not
have the ``.ny`` extension. This is checked before the file is opened.

Neighboring codes: this error arises only for file names on the command line.
The ``import`` command always appends ``.ny`` to its argument, so ``import
"foo.txt"`` looks for ``foo.txt.ny`` and gives ``E2304`` if that file cannot
be opened.

**Example**

.. code-block:: none

   $ echo 'axiom A : Type' > foo.txt
   $ narya foo.txt

   ￫ error[E2302]
   ￮ filename 'foo.txt' does not have 'ny' extension

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2304"><summary><code>E2304</code> No_such_file</summary>

This error is reported when a file named on the command line or in an
``import`` command cannot be opened, usually because it does not exist. The
command ``import "name"`` looks for the file ``name.ny`` relative to the
directory of the importing file; in an ``-e`` string or in interactive input,
relative to the current directory, which ``chdir`` changes. The message shows
the full path of the file that Narya tries to open.

Neighboring codes: ``E2302`` if a file named on the command line does not have
the ``.ny`` extension.

**Example**

.. code-block:: none

   import "nofile"

   ￫ error[E2304]
   ￮ error opening file: …/nofile.ny

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2306"><summary><code>E2306</code> Library_modified</summary>

This error is reported when a file that was already loaded earlier in the same
session is imported again, but it, or one of the files it imports, has been
modified on disk since it was loaded. Narya does not reload files within a
session, so the session must be restarted to use the new version. The file
named in the message is the one that has changed. This arises in long-running
sessions, that is, in interactive mode or ProofGeneral mode.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E25xx: Undo (interactive mode)</h2>

.. raw:: html

   <details class="error-code" id="E2500"><summary><code>E2500</code> Not_enough_to_undo</summary>

This error is reported when the ``undo`` command is asked to undo more
commands than have been executed interactively in the current session. Only
commands entered in interactive mode can be undone, not those loaded from
files or ``-e`` strings. Commands that failed are not counted, and neither are
commands that do not change the state, such as ``echo``, ``show`` and
``solve``.

After this error, later commands in the same session currently fail with an
``E0000`` anomaly; this is a bug in Narya, and the session has to be
restarted.

Neighboring codes: ``E2001`` if ``undo`` appears in a file or an ``-e``
string.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E26xx: Sections</h2>

.. raw:: html

   <details class="error-code" id="E2600"><summary><code>E2600</code> No_such_section</summary>

This error is reported when an ``end`` command is given when no section is
open. Every ``end`` closes the most recently opened ``section`` that is still
open, and sections do not extend from one file into another.

Neighboring codes: an invalid name in a ``section`` command is ``E2601``.

**Example**

.. code-block:: none

   end

   ￫ error[E2600]
   ￮ no section here to end

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E2601"><summary><code>E2601</code> Invalid_section_name</summary>

This error is reported when the name given to a ``section`` command cannot be
used as a section prefix. Either one of its components is not a valid
identifier, for instance because it begins with an underscore or consists only
of digits, or it contains the component ``notations``, which is used for the
namespace in which notations are stored.

Neighboring codes: ``E2600`` for an ``end`` without an open section.

**Example**

.. code-block:: none

   section notations :=

   ￫ error[E2601]
   ￮ invalid section name: notations

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E30xx: Interactive proof</h2>

.. raw:: html

   <details class="error-code" id="E3001"><summary><code>E3001</code> No_such_hole</summary>

This error is reported when a command refers to a hole number that does not
correspond to any open hole: the hole never existed, has already been solved,
or the command that created it has been undone. Hole numbers are not reused.
The commands concerned are ``solve``, ``split``, ``show hole``, ``echo in``,
``synth in`` and ``about in``.

Neighboring codes: these commands are only meaningful interactively, and
elsewhere ``show hole`` gives ``E2001``. The others look up the hole while
they are parsed, so in a file or an ``-e`` string they report this error when
the hole does not exist, as in the example below. When the hole does exist,
they currently fail there with the ``E0000`` anomaly ``timeless hole``
instead; this is a bug in Narya.

**Example**

.. code-block:: none

   solve 0 ≔ Type

   ￫ error[E3001]
   ￮ no open hole numbered 0

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E3002"><summary><code>E3002</code> Open_holes_remaining</summary>

This error is reported when a file, standard input or an ``-e`` string is
processed completely but still contains unsolved holes ``?``. The definitions
are checked, but Narya exits with an error. This happens for every
command-line input, even when ``-i`` or ``-proofgeneral`` is also given: holes
can be left open only in commands that are entered interactively. The types of
the holes are shown only with ``-v``.

Neighboring codes: ``E2002`` for a hole in a file that is loaded with
``import``.

**Example**

.. code-block:: none

   echo (? : Type)

   ?0
    : Type

   ￫ error[E3002]
   ￮ command-line exec string contains open holes

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E31xx: Errors from external clients</h2>

.. raw:: html

   <details class="error-code" id="E3100"><summary><code>E3100-…</code> Extern</summary>

This is an error reported not by Narya itself but by an external program that
uses Narya as a library. Such a client supplies its own sub-code and message
text, and the sub-code is appended to ``E3100-``. The ``narya`` executable
never produces this error.

Neighboring codes: ``E3200`` is the other code reserved for such clients.

.. raw:: html

   </details>

.. raw:: html

   <h2 class="error-group">E32xx: Oracles</h2>

.. raw:: html

   <details class="error-code" id="E3200"><summary><code>E3200</code> Oracle_failed</summary>

A program that uses Narya as a library can install an oracle, which is
consulted during typechecking and may reject terms. This code reports such a
rejection; the message is just ``oracle failed``. The oracle installed by the
``narya`` executable accepts everything, so the executable never produces this
error.

Neighboring codes: errors that a client detects by itself are reported as
``E3100-…``.

.. raw:: html

   </details>

