Contributing to Narya
=====================

Contributions to Narya are welcome!  If you have code you want to contribute, please fork the `GitHub repository <https://github.com/gwaithimirdain/narya>`_ and create a pull request.  If you aren't sure whether some contribution would be accepted, you may want to open a GitHub issue first to discuss it.

Please format OCaml code using ``ocamlformat`` with the options in the supplied ``.ocamlformat`` file.  Please format Narya code (such as cram tests in the ``test/`` directory) using Narya's built-in formatter.  (Not all the existing tests are currently formatted that way, as they predate the formatter.)  Please format Emacs Lisp code (for the ProofGeneral mode) using Emacs' indentation functions such as ``C-M-q``, with ``indent-tabs-mode`` *off*.

Please try to keep your git history relatively clean, but don't waste a lot of time on it.  The most useful thing to do is ensure that each commit individually builds succesfully (and ideally passes all the tests, although that is more negotiable), as that makes it easier to use ``git bisect`` when necessary.

Narya is licensed under the GPL v3.0.  When submitting a pull request, you retain the copyright to your code, but you consent to its distribution in perpetuity under this license or any other open-source license that may later be adopted by the maintainers.

