Installation
============

From source
------------

There is no distribution yet, so you have to compile Narya yourself.  This requires a recent version of OCaml and various libraries.  Currently Narya is developed with OCaml 5.3.0; as far as I know, it also compiles with any version after 5.2.1, but this is not regularly verified.  After installing any version of OCaml and its package manager Opam, you can install Narya with its dependencies as follows:

.. code-block:: bash

    opam switch create 5.3.0
    opam install dune

    cd narya
    dune build narya.opam
    opam install . --deps-only
    dune build @install
    dune runtest
    dune install

This will make the executable ``narya`` available in a directory such as ``~/.opam/5.3.0/bin``, which should be in your ``PATH``.  Alternatively, instead of ``dune install`` you can also run the executable directly from the ``narya/`` directory with ``dune exec narya``.  In this case, to pass flags to the executable, put them after a ``--``.  For instance, ``dune exec narya -- test.ny -i`` loads the file ``test.ny`` and then enters interactive mode.

ProofGeneral (Emacs) mode
-------------------------

The recommended mode of use of Narya is with its `ProofGeneral <https://proofgeneral.github.io/>`_ Emacs mode (for further description of this, see below).  Unfortunately, ProofGeneral is not well-designed for users adding new proof assistant modes.  The steps to install Narya's ProofGeneral mode are:

1. Install Emacs and ProofGeneral.  The recommended way to install ProofGeneral is from `MELPA <https://melpa.org/>`_ using Emacs' package manager, as described at the `ProofGeneral page <https://proofgeneral.github.io/>`_.

2. Find the ProofGeneral installation directory, which may be something like ``$HOME/.emacs.d/elpa/proof-general-XXXXXXXX-XXXX``.

3. In this directory, create a subdirectory called ``narya`` and copy (or, better, symlink) the files in the proofgeneral directory of the Narya repository into that subdirectory.

4. Then edit the file ``proof-site.el`` in the subdirectory ``generic`` of the ProofGeneral installation directory and add a line containing ``(narya "Narya" "ny" nil (".nyo"))`` to the list of proof assistants in the definition of the variable ``proof-assistant-table-default``.

5. If there is a byte-compiled Emacs Lisp file ``proof-site.elc`` in the ``generic`` directory, either delete it, or re-create it from your edited ``proof-site.el`` using ``M-x byte-compile-file``.

6. Restart Emacs.

You will have to repeat these steps whenever the Narya ProofGeneral mode is updated (unless you symlinked the files instead of copying them, in which case restarting Emacs will suffice); whenever ProofGeneral is updated; and whenever Emacs is updated.  Note also that you can only use ProofGeneral with one proof assistant per Emacs session: if you want to switch between (say) Narya and Rocq, you need to restart Emacs or open a new instance of it.  These appear to be fundamental restrictions of ProofGeneral (if you know how to get around them, please let me know); although once Narya and its ProofGeneral mode are more stable we can probably petition to be added to the main ProofGeneral distribution.

In-browser version
------------------

There is also a version of Narya that compiles to JavaScript and runs in a browser, called jsNarya.  Instructions for compiling and running jsNarya locally can be found in `js/README <https://github.com/gwaithimirdain/narya/blob/master/js/README.md>`_, but a recent version of it can also be accessed directly at `mikeshulman.github.io/jsnarya <https://mikeshulman.github.io/jsnarya>`_, not requiring installing or compiling anything locally.  However, jsNarya is currently limited to the interactive mode with one startup file (:ref:`see here <top-level-interface-jsNarya>`).

