Error codes
===========

This page lists the error codes that Narya can report. Click on a code to see
a minimal example that triggers it and a way to fix it.

The examples can be reproduced from the command line with ``narya -e "..."``.

Errors are grouped by the first two digits of their code.

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

Not yet documented:

- ``E0000`` Anomaly
- ``E0001`` No_such_level
- ``E0002`` Accumulated
- ``E0003`` Invalid_degeneracy_action

.. raw:: html

   <h2 class="error-group">E01xx: Unimplemented or deprecated features</h2>

Not yet documented:

- ``E0100`` Unimplemented
- ``E0110`` Deprecated

.. raw:: html

   <h2 class="error-group">E02xx: Parse errors</h2>

.. raw:: html

   <details class="error-code" id="E0200"><summary><code>E0200</code> Parse_error</summary>

The input is not a valid Narya syntax. Typical reasons are unbalanced
parentheses, a missing ``≔``, an operator that is not a defined notation, or a
field projection with nothing in front of it. The reported location is the first token that the parser 
cannot interpret. In the case of an extra or misplaced token, this is the 
error itself; in the case of a missing element (such as an unclosed parenthesis), 
it is the token immediately following the incomplete expression, 
which may appear on a subsequent line.

**Examples**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom x : A
   echo f (x
   
   ￫ error[E0200]
   ￭ command-line exec string
   5 | ‹EOF›
     ^ parse error: invalid syntax

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom x : A
   echo f (x) )

   ￫ error[E0200]
   ￭ command-line exec string
   4 | echo f (x) )
     ^ parse error: invalid syntax

**Fix**

Complete the expression, and make sure it is part of a command such as
``echo`` or ``def``. 

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   axiom x : A
   echo f (x)

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0202"><summary><code>E0202</code> Invalid_variable</summary>

A local variable name (bound by ``let``, ``↦``, a ``match`` pattern, or the
``variables`` attribute) is not a valid identifier. Local names must not
contain a period, and ``_`` cannot be used as a name in some positions.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A → A
   notation(0) x "&" y.z := f x y.z
   
   ￫ error[E0202]
   ￭ command-line exec string
   3 |    notation(0) x "&" y.z := f x y.z
     ^ invalid local variable name: y.z

**Fix**

Use a name without periods. Dotted names are reserved for constants living
in namespaces.

.. code-block:: none

   axiom A : Type
   axiom f : A → A → A
   notation(0) x "&" y ≔ f x y

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0203"><summary><code>E0203</code> Invalid_field</summary>

A field projection such as ``x .fs.t`` is not a valid field name. After the
leading period, a field name may be followed only by numeric suffixes (as in
``.fst.1``), not by further alphabetic components.

**Example**

.. code-block:: none

   echo (x |-> x .fs.t y)

   ￫ error[E0203]
   ￭ command-line exec string
   1 | echo (x |-> x .fs.t y)
     ^ invalid field name: .fs.t

**Fix**

Project a single field at a time.

.. code-block:: none

   def B : Type ≔ sig (fst : Type)
   def g (b : B) : Type ≔ b .fst

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0205"><summary><code>E0205</code> Invalid_numeral</summary>

A token that starts with a digit is not a well-formed numeral. Numerals may
contain at most one period (for future decimal support); something like
``0.1.2`` is rejected.

**Example**

.. code-block:: none

   axiom A : Type
   axiom f : A → A
   echo (x |-> f 0.1.2 x)

   ￫ error[E0205]
   ￭ command-line exec string
   3 | echo (x |-> f 0.1.2 x)
     ^ invalid numeral: 0.1.2

**Fix**

Write a plain numeral, and assign it to a type with `zero.` and `suc.` 
constructors so that it can be checked.

.. code-block:: none

   def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]
   echo (12 : ℕ)

.. raw:: html

   </details>

.. raw:: html

Not yet documented:

- ``E0201`` Break
- ``E0201`` Parsing_ambiguity
- ``E0204`` Invalid_constr
- ``E0206`` Invalid_degeneracy
- ``E0207`` No_relative_precedence
- ``E0208`` Unrecognized_attribute
- ``E0250`` Comment_end_in_string
- ``E0280`` Cyclic_term
- ``E0299`` Encoding_error

.. raw:: html

   <h2 class="error-group">E03xx: Scope errors</h2>

.. raw:: html

   <details class="error-code" id="E0300"><summary><code>E0300</code> Unbound_variable</summary>

A name is used that is neither a local variable in scope nor a defined
constant. When a similar name exists, the message suggests it in a hint (see E2100).

**Example**

.. code-block:: none

   echo g

   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo g
     ^ unbound variable: g

**Fix**

Define or import the name before using it, or check the spelling and the
namespace (for example ``ℤ.zero`` versus ``ℤ .zero``).

.. code-block:: none

   axiom g : Type
   echo g

.. raw:: html

   </details>

.. raw:: html

   <details class="error-code" id="E0311"><summary><code>E0311</code> Locked_constant</summary>

A constant that is, or depends on, a ``#(nonparametric)`` axiom is used
inside an external degeneracy such as ``A⁽ᵈ⁾``. Nonparametric axioms have no
higher-dimensional structure, so this is not allowed. This error only arises
in modal type theories such as ``-dtt``.

**Example**

Run this example with the ``-dtt`` flag. Without it, the degeneracy ``d`` is
not recognized and the error reported is ``E0206`` instead.

.. code-block:: none

   axiom #(nonparametric) A : Type
   echo A⁽ᵈ⁾

   ￫ error[E0311]
   ￭ command-line exec string
   1 | echo A⁽ᵈ⁾
     ^ constant A is or uses a nonparametric axiom, can't appear inside an external degeneracy

**Fix**

Either declare the axiom as parametric (drop the attribute), or avoid
applying an external degeneracy to anything built from it.

.. code-block:: none

   axiom A : Type
   echo A⁽ᵈ⁾

.. raw:: html

   </details>

Not yet documented:

- ``E0301`` Undefined_constant
- ``E0302`` Undefined_metavariable
- ``E0303`` Ill_scoped_connection
- ``E0304`` Unattached_assumption
- ``E0310`` Locked_variable
- ``E0312`` Axiom_in_parametric_definition
- ``E0313`` Hidden_variable

.. raw:: html

   <h2 class="error-group">E04xx: Bidirectional typechecking and case trees</h2>

Not yet documented:

- ``E0400`` Nonsynthesizing
- ``E0401`` Unequal_synthesized_type
- ``E0402`` Synthesizing_recursion
- ``E0404`` Invalid_synthesized_type
- ``E0405`` Type_expected

.. raw:: html

   <h2 class="error-group">E05xx: Dimensions</h2>

Not yet documented:

- ``E0500`` Dimension_mismatch
- ``E0501`` Not_enough_lambdas
- ``E0502`` Not_enough_arguments_to_function
- ``E0503`` Not_enough_arguments_to_instantiation
- ``E0504`` Type_not_fully_instantiated
- ``E0505`` Instantiating_zero_dimensional_type
- ``E0506`` Invalid_variable_face
- ``E0508`` Zero_dimensional_cube_abstraction
- ``E0509`` Mismatched_dimensions_in_cube_abstraction
- ``E0510`` Noncube_abstraction_in_higher_dimensional_match
- ``E0511`` Invalid_flags

.. raw:: html

   <h2 class="error-group">E06xx: Degeneracies</h2>

Not yet documented:

- ``E0600`` Missing_argument_of_degeneracy
- ``E0601`` Low_dimensional_argument_of_degeneracy
- ``E0602`` Low_dimensional_type_of_degeneracy

.. raw:: html

   <h2 class="error-group">E07xx: Function types</h2>

Not yet documented:

- ``E0700`` Checking_lambda_at_nonfunction
- ``E0701`` Applying_nonfunction_nontype
- ``E0702`` Unexpected_implicitness
- ``E0703`` Insufficient_dimension
- ``E0704`` Unequal_synthesized_boundary
- ``E0705`` Not_enough_domains
- ``E0706`` Invalid_higher_function
- ``E0707`` Invalid_nullary_application
- ``E0708`` Expected_nullary_application

.. raw:: html

   <h2 class="error-group">E08xx: Record fields</h2>

Not yet documented:

- ``E0800`` No_such_field
- ``E0801`` Wrong_dimension_of_field
- ``E0802`` Invalid_field_suffix

.. raw:: html

   <h2 class="error-group">E09xx: Tuples</h2>

Not yet documented:

- ``E0900`` Checking_tuple_at_nonrecord
- ``E0901`` Checking_tuple_at_degenerated_record
- ``E0902`` Missing_field_in_tuple
- ``E0903`` Extra_field_in_tuple
- ``E0904`` Duplicate_field_in_tuple
- ``E0905`` Invalid_field_in_tuple

.. raw:: html

   <h2 class="error-group">E10xx: Datatype constructors</h2>

Not yet documented:

- ``E1000`` No_such_constructor
- ``E1001`` Wrong_number_of_arguments_to_constructor
- ``E1002`` Missing_instantiation_constructor
- ``E1003`` Unequal_indices

.. raw:: html

   <h2 class="error-group">E11xx: Matches: match variable</h2>

Not yet documented:

- ``E1100`` Unnamed_variable_in_match
- ``E1101`` Matching_wont_refine

.. raw:: html

   <h2 class="error-group">E12xx: Matches: match type</h2>

Not yet documented:

- ``E1200`` Matching_on_nondatatype
- ``E1201`` Matching_datatype_has_degeneracy

.. raw:: html

   <h2 class="error-group">E13xx: Matches: match branches</h2>

Not yet documented:

- ``E1300`` Missing_constructor_in_match
- ``E1301`` No_such_constructor_in_match
- ``E1302`` Duplicate_constructor_in_match
- ``E1303`` Wrong_number_of_arguments_to_pattern
- ``E1304`` Duplicate_pattern_variable
- ``E1305`` Wrong_number_of_patterns
- ``E1306`` Inconsistent_patterns
- ``E1307`` Overlapping_patterns
- ``E1308`` No_remaining_patterns
- ``E1309`` Invalid_refutation

.. raw:: html

   <h2 class="error-group">E14xx: Match motives and comatches</h2>

Not yet documented:

- ``E1400`` Comatching_at_noncodata
- ``E1400`` Wrong_number_of_arguments_to_motive
- ``E1401`` Comatching_at_degenerated_codata
- ``E1402`` Missing_method_in_comatch
- ``E1403`` Extra_method_in_comatch
- ``E1404`` Duplicate_method_in_comatch
- ``E1405`` Invalid_method_in_comatch

.. raw:: html

   <h2 class="error-group">E15xx: Canonical types</h2>

Not yet documented:

- ``E1500`` Checking_canonical_at_nonuniverse
- ``E1501`` Duplicate_field_in_record
- ``E1502`` Duplicate_method_in_codata
- ``E1503`` Duplicate_constructor_in_data
- ``E1504`` Wrong_boundary_of_record
- ``E1505`` Invalid_constructor_type
- ``E1506`` Missing_constructor_type
- ``E1507`` Lower_and_higher_methods_in_codata
- ``E1508`` Invalid_self_variable_type

.. raw:: html

   <h2 class="error-group">E16xx: Tactics</h2>

Not yet documented:

- ``E1600`` Choice_mismatch
- ``E1601`` Calc_error

.. raw:: html

   <h2 class="error-group">E17xx: Modal type theory</h2>

Not yet documented:

- ``E1700`` Mode_mismatch
- ``E1701`` Modality_mismatch
- ``E1702`` Modalcell_mismatch
- ``E1703`` Non_mode_synthesizing
- ``E1704`` Unknown_modality
- ``E1705`` Missing_key
- ``E1706`` Intangible_modality
- ``E1706`` Unknown_modalcell
- ``E1707`` Key_mismatch
- ``E1707`` Nontransparent_window_modality
- ``E1708`` Nonparametric_mode_degeneracy
- ``E1710`` Invalid_mode_theory
- ``E1711`` Modality_not_sinister
- ``E1712`` Wrong_locking_modality
- ``E1713`` Modal_field_filtered_away
- ``E1714`` Extra_filtered_field_in_tuple

.. raw:: html

   <h2 class="error-group">E20xx: Commands</h2>

Not yet documented:

- ``E2000`` Too_many_commands
- ``E2001`` Forbidden_interactive_command
- ``E2002`` No_holes_allowed
- ``E2003`` Invalid_instant

.. raw:: html

   <h2 class="error-group">E21xx: Defining constants</h2>

Not yet documented:

- ``E2100`` Redefining_constant
- ``E2101`` Invalid_constant_name

.. raw:: html

   <h2 class="error-group">E22xx: Notation definitions</h2>

Not yet documented:

- ``E2200`` Invalid_tightness
- ``E2201`` Invalid_notation_symbol
- ``E2202`` Invalid_notation_pattern
- ``E2203`` Fixity_mismatch
- ``E2204`` Duplicate_notation_variable
- ``E2205`` Invalid_notation_head
- ``E2206`` Unused_notation_variable
- ``E2207`` Notation_variable_used_twice
- ``E2208`` Unbound_variable_in_notation
- ``E2209`` Head_already_has_notation

.. raw:: html

   <h2 class="error-group">E23xx: Imports and files</h2>

Not yet documented:

- ``E2300`` Circular_import
- ``E2302`` Invalid_filename
- ``E2304`` No_such_file
- ``E2306`` Library_modified

.. raw:: html

   <h2 class="error-group">E25xx: Undo (interactive mode)</h2>

Not yet documented:

- ``E2500`` Not_enough_to_undo

.. raw:: html

   <h2 class="error-group">E26xx: Sections</h2>

Not yet documented:

- ``E2600`` No_such_section
- ``E2601`` Invalid_section_name

.. raw:: html

   <h2 class="error-group">E30xx: Oracles and interactive proof</h2>

Not yet documented:

- ``E3000`` Oracle_failed
- ``E3001`` No_such_hole
- ``E3002`` Open_holes_remaining
