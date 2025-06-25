Installation
============

There are several ways to install Narya.

- If you are using Linux, or on Windows and you have (or can install) WSL, and you don't want to edit or contribute to the Narya source code, the easiest way to run Narya is to use the :ref:`Static binary`.
- If you are on MacOS, or you want to edit the Narya source code, you'll need :ref:`Compiling from source` instead.
- You can also use an in-browser version called :ref:`Installing jsNarya` without installing anything, although its functionality is limited and the currently posted version is out of date.

In addition to installing the basic Narya executable, the following are highly recommended:

- The :ref:`Installing ProofGeneral mode` that runs inside Emacs.
- Further :ref:`Configuration` options.

We have tried to make the installation process as easy and painless as possible.  If you run into any problems, please ask for help!  See :ref:`Support and community` for places to ask.


Static binary
-------------

A statically compiled binary, built automatically with Nix from the up-to-date development version, can be downloaded `here <https://gwaithimirdain.github.io/narya/releases/narya-master-static.tar.gz>`_.  This ought to work on any Linux computer, including on Windows using WSL (see :ref:`On Windows`).

On Linux
^^^^^^^^

After downloading and unpacking the `static distribution <https://gwaithimirdain.github.io/narya/releases/narya-master-static.tar.gz>`_, place the ``narya`` executable in a directory that's in your ``PATH`` (the "environment variable" that tells your shell or command prompt which directories to look in to find programs).  On some flavors of Linux, the directory ``~/bin`` is automatically in your path if it exists, so the first thing to try is

.. code-block:: bash

  mkdir -p ~/bin
  cp narya ~/bin

Then restart your shell (i.e. terminal or command prompt) and try running ``narya``.  If that doesn't work, try logging out and back in again.  If that still doesn't work, try something like the following:

.. code-block:: bash

  echo export PATH="\$HOME/bin:\$PATH" >>~/.bashrc

and then once again restart your shell, or log out and back in again.

Once you can run Narya from the command prompt, proceed to :ref:`Installing ProofGeneral mode`.


On Windows
^^^^^^^^^^

The easiest way to run Narya on Windows 11 is to use the static binary inside `Windows Subsystem for Linux <https://learn.microsoft.com/en-us/windows/wsl/install>`_.  To install WSL, open a command prompt and run

.. code-block:: none

  wsl --install

After this finishes, you may need to reboot your computer and run the same command again in order to install a Linux distribution inside WSL.  Once WSL is installed, you can run

.. code-block:: none

  wsl

to enter a Linux command prompt, and then follow the :ref:`On Linux` instructions above.  If you downloaded the static distribtion in Windows, you can usually navigate to it in WSL using a path like ``/mnt/c/Users/YOUR NAME/Downloads``.  You can also download it directly from the WSL prompt with

.. code-block:: none

  wget https://gwaithimirdain.github.io/narya/releases/narya-master-static.tar.gz
  tar -xzf narya-master-static.tar.gz
  cd narya-xxxxxxx-YYYYMMDD

(for the appropriate directory name) and then proceed with the above Linux instructions (and the later instructions for :ref:`Installing ProofGeneral mode`).  Note that when you run Emacs from the WSL command prompt, it should automatically pop up as a graphical window; you can run ``emacs &`` if you want to also continue using your command prompt while Emacs is running.


On Mac
^^^^^^

The static binary does not work on a Mac, but you can compile Narya from source as below.


Compiling from source
---------------------

If the static binary does not work for you (such as if you are on MacOS), or if you want to edit the Narya code, you will have to compile it yourself.  This requires a recent version of OCaml and various libraries.  Currently Narya is developed with OCaml 5.3.0; as far as I know, it also compiles with any version after 5.2.1, but this is not regularly verified.  You can set up a :ref:`Manual development environment` or look into :ref:`Compiling with nix`.


Manual development environment
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Here are steps to manually set up a development environment in which you can compile Narya.

1. Install `OCaml <https://ocaml.org/>`_ and its package manager `Opam <https://opam.ocaml.org/>`_.  How to do this this may vary depending on your operating system.  Make sure that the opam bin directory is permanently added to the ``PATH`` in your shell; if you run ``opam init`` (*not* ``opam init -y``) it will offer to do that for you.

2. Set up the OCaml environment and install the Dune build system by running the following commands:

  .. code-block:: bash

    opam switch create 5.3.0
    opam install dune
    eval $(opam env)

  The ``eval`` command is for Unix-like operating systems.  On Windows, replace it by:

  .. code-block:: none

    for /f "tokens=*" %i in ('opam env') do @%i

  or for PowerShell:

  .. code-block:: none

    (& opam env) -split '\r?\n' | ForEach-Object { Invoke-Expression $_ }

3. Download the Narya source code.  If you have (or install) `Git <https://git-scm.com/>`_ you can do this with:

  .. code-block:: bash

    git clone https://github.com/gwaithimirdain/narya.git

  You can also download a `ZIP file <https://github.com/gwaithimirdain/narya/archive/refs/heads/master.zip>`_ and unpack it.

4. Navigate to the root of the Narya source code (e.g. ``cd narya`` or ``cd narya-master``) and run the following commands:

  .. code-block:: bash

    dune build narya.opam
    opam install . --deps-only
    dune build @install
    dune runtest
    dune install

This will make the executable available in a directory such as ``$HOME/.opam/5.3.0/bin``.  If Opam was installed correctly using ``opam init``, this directory should already be in your ``PATH``, so that you can then run Narya in the future from any directory by simply typing ``narya``.

Alternatively, instead of running ``dune install``, you can run the executable directly from the Narya source directory with ``dune exec narya``.  In this case, to pass flags to the executable, put them after a ``--``.  For instance, ``dune exec narya -- test.ny -i`` loads the file ``test.ny`` and then enters interactive mode.

If any of the above steps don't work for you, or if you have any other problems or encounter any bugs, please let us know by `opening an issue on GitHub <https://github.com/gwaithimirdain/narya/issues/new/choose>`_.

Compiling with nix
^^^^^^^^^^^^^^^^^^

Narya can also be developed and installed with `Nix <https://nixos.org/>`_, which can automatically set up a development environment for you, and also build static binaries.  (However, Nix is not well-supported by the Narya developers, so you may be on your own.)

1. Get a version of nix with `flakes <https://nixos.wiki/wiki/flakes>`_ enabled, for instance via `determinate nix <https://github.com/DeterminateSystems/nix-installer>`_.

2. Run ``nix develop`` to open a shell with all of the necessary dependencies for running ``dune build``. This may ask if you accept using a cache; you can say yes if you want to speed up the build process, or no if you want everything built on your own machine.

3. To build a static executable that can be copied over to other Linux machines without problems (like the one mentioned above that is built automatically and hosted on github), run the following command in the Narya source directory.

.. code-block:: bash

  GIT_COMMIT=`git show -s --format=%h` nix build --impure

Running just ``nix build`` instead will still build a static binary that will work, but it will not know what git commit it was built from.  This has two consequences: it will not report that commit when run with the ``-version`` flag (making it harder to track down any bugs it exhibits); and it will not be able to tell whether compiled ``.nyo`` files are compatible (and therefore will never load them).


Building the Documentation
^^^^^^^^^^^^^^^^^^^^^^^^^^

The most recent version of the documentation is automatically posted on `ReadtheDocs <https://narya.readthedocs.io/en/latest/>`_, so even if you are compiling Narya locally, it is not necessary to also build the documentation locally, unless you want to contribute to it or have it available offline.  To build the documentation locally, ensure you have the following dependencies installed:

1. *Sphinx*: The documentation generator.
2. *Sphinx Read the Docs theme*: A popular theme for Sphinx-based documentation.

To install these dependencies, run the following commands:

.. code-block:: bash
   
   pip install sphinx sphinx-rtd-theme

After installing the required dependencies, navigate to the documentation directory (typically ``docs/`` or ``docs/source/``).

To build the documentation in HTML format, run:

.. code-block:: bash
   
   make html

The output will be saved in the ``_build/html`` directory. You can open ``index.html`` in a browser to view the documentation.

For more advanced configuration, refer to the `Sphinx documentation <https://www.sphinx-doc.org/>`_


.. _Installing jsNarya:

jsNarya
-------

jsNarya is also a version of Narya that compiles to JavaScript and runs in a browser, although it is currently limited to the interactive mode with one startup file (:ref:`see here <jsNarya>`).  A somewhat outdated version of jsNarya can be accessed directly at `mikeshulman.github.io/jsnarya <https://mikeshulman.github.io/jsnarya>`_, not requiring installing or compiling anything locally.  Instructions for compiling and running jsNarya locally can be found in `js/README <https://github.com/gwaithimirdain/narya/blob/master/js/README.md>`_.


.. _Installing ProofGeneral mode:

ProofGeneral Mode
-----------------

`ProofGeneral <https://proofgeneral.github.io/>`_ is a generic development environment designed for proof assistants that runs inside the text editor Emacs.  Narya comes with a basic ProofGeneral mode that is the recommended way to use it.

To install the Narya ProofGeneral mode, first you'll need to install a relatively recent version of `Emacs <https://www.gnu.org/software/emacs/>`_.  Unfortunately, the version installable through the default package manager on many Linux distributions (such as ``apt`` on Debian/Ubuntu) is not recent enough.  However, on many modern Linux distributions (including WSL) you can install a more recent version of Emacs with

.. code-block:: bash

  sudo snap install emacs --classic

If you have previously installed an older version of Emacs through your package manager, you may want to remove it (such as with ``sudo apt remove emacs-common``) to avoid confusion, and then restart your shell or terminal.  To find out what version of Emacs you have, you can run ``emacs --version`` in a terminal, or ``M-x emacs-version`` inside Emacs: look for at least 30.1.

Once Emacs is installed, you have two options for installing the Narya ProofGeneral mode:

- There is an :ref:`Automatic ProofGeneral installation` script that should usually be able to install ProofGeneral and the Narya ProofGeneral mode for you, once you have installed Emacs.
- If this doesn't work, or you want to edit the Narya ProofGeneral mode, you can use :ref:`Manual ProofGeneral installation` instead.


.. _Automatic ProofGeneral installation:

Automatic installation
^^^^^^^^^^^^^^^^^^^^^^

Narya comes with a shell script that should install ProofGeneral, and the ProofGeneral Narya mode, on any machine where Emacs is already installed, including Linux, Windows with WSL, and MacOS.  The script is called ``install-pg.sh``; it is included in the static distribution, while in the source repository it is in the subdirectory ``dist``.  In either case, navigate to the directory that contains the script and run it with:

.. code-block:: bash

  ./install-pg.sh

If the script reports any errors, or if it doesn't report any errors but the ProofGeneral mode doesn't seem to work as advertised, please report a bug on `GitHub <https://github.com/gwaithimirdain/narya>`_; in the meantime, you can follow the instructions for :ref:`Manual ProofGeneral installation`.

You will also need to ensure that Emacs can find the Narya executable.  On Linux machines, and on Windows with WSL, this should happen automatically as long as the directory containing narya is in your ``PATH``.  On a Mac, when Emacs is run as a GUI it takes its environment variables from somewhere else, so it may not be able to find Narya; one solution is to install the package `exec-path-from-shell <https://github.com/purcell/exec-path-from-shell>`_.

You will need to re-run the installation script every time Emacs, ProofGeneral, or Narya is updated.  This will be the case until the Narya ProofGeneral mode stabilizes and we can get it incorporated in the ProofGeneral distribution.

Once ProofGeneral is installed and working, you can proceed with further :ref:`Configuration`.


.. _Manual ProofGeneral installation:

Manual installation
^^^^^^^^^^^^^^^^^^^

If the automatic ProofGeneral installer doesn't work for you, you can follow these steps to install Narya's ProofGeneral mode manually.

1. Install `Emacs <https://www.gnu.org/software/emacs/>`_ and ProofGeneral.  The recommended way to install ProofGeneral is from `MELPA <https://melpa.org/>`_ using Emacs' package manager, as described at the `ProofGeneral page <https://proofgeneral.github.io/>`_.

2. Find the ProofGeneral installation directory, which may be something like ``$HOME/.emacs.d/elpa/proof-general-XXXXXXXX-XXXX``.

3. In this directory, create a subdirectory called ``narya`` and copy (or, better, symlink) the ``.el`` files in the ``proofgeneral`` directory of the Narya repository into that subdirectory.  If you are using the static distribution, the ``.el`` files are included there as well.

4. Edit the file ``proof-site.el`` in the subdirectory ``generic`` of the ProofGeneral installation directory and add this line

  .. code-block:: none

    (narya "Narya" "ny" nil (".nyo"))

  to the list of proof assistants in the definition of the variable ``proof-assistant-table-default``.

5. If there is a byte-compiled Emacs Lisp file ``proof-site.elc`` in the ``generic`` directory, either delete it, or re-create it from your edited ``proof-site.el`` using ``M-x byte-compile-file``.

6. Restart Emacs.

You will have to repeat these steps whenever the Narya ProofGeneral mode is updated (unless you symlinked the files instead of copying them, in which case restarting Emacs will suffice); whenever ProofGeneral is updated; and whenever Emacs is updated.

Once ProofGeneral is installed and working, you can proceed with further :ref:`Configuration`.


Configuration
-------------

Once Narya and its ProofGeneral mode are installed, you can run

.. code-block:: bash

  emacs

Then whenever you create or open a ``.ny`` file in Emacs, Narya ProofGeneral should automatically start.  The first time you do this, look in the minibuffer (at the bottom of the screen) for any errors or warning messages that may indicate a problem with the installation of Narya, Emacs, or ProofGeneral.  For usage instructions, see :ref:`ProofGeneral mode`.  You should also familiarize yourself with the standard syntax for `Emacs key sequences <https://www.gnu.org/software/emacs/manual/html_node/emacs/User-Input.html>`_ such as ``C-c C-M-a``.

Note that you can only use ProofGeneral with one proof assistant per Emacs session: if you want to switch between (say) Narya and Rocq, you need to restart Emacs each time, or open a separate instance of it for each proof assistant.

There are also a few additional configuration actions that are highly recommended for usability.


Configuration variables
^^^^^^^^^^^^^^^^^^^^^^^

Here are some other ProofGeneral customization options that are highly recommended.  These can be set in Emacs using ``M-x customize-variable RET``, then enter the variable name and hit enter.  In the resulting customization buffer, select the value you want for the variable, then click ``State`` and select ``Save for future sessions``; this will automatically write some code to your Emacs initialization file.

- ``proof-output-tooltips``: You should turn this off (``nil``), as the "output" that it displays in tooltips is not very readable or helpful.

- ``proof-three-window-mode-policy``: Assuming your screen is significantly wider than it is tall, as most computer screens are, it is highly recommended to set this to ``Horizontal (two columns)``, so that the goals and response buffers do not take up vertical space.  (The configuration option ``proof-three-window-enable`` must also be set to on (``non-nil``), although this is usually the default so you shouldn't have to touch it.)

- ``narya-prog-args``: If you want to pass command-line options to alter the behavior of Narya, such as options like ``-hott`` that modify the type theory, at present the only way to do this is to change this variable.  You can do that globally with ``customize-variable``, or locally in particular ``ny`` files with Emacs file-local variables.  If you do change this variable, make sure to keep the argument ``-proofgeneral`` in it, which is necessary to put Narya into the correct mode for interacting with ProofGeneral.  As an example, to set the option ``-hott`` locally in a file, you can insert the following as its first line:

  .. code-block:: none

     {` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

  This file-local approach does have some pitfalls.  For instance, if you start processing one file, then retract it completely and start processing another file, ProofGeneral does not restart Narya, so the flags passed by the first file will remain in effect.  You must also agree every time you open a file like this to execute the "unsafe" file-local variable, or else mark it as permanently trusted -- and don't mark it as permanently untrusted, or it'll stop working completely.


Entering Unicode characters
^^^^^^^^^^^^^^^^^^^^^^^^^^^

When coding with Narya in Emacs, you will often want an *input mode* that enables special key sequences for inserting Unicode characters, usually using TeX-style keyboard shortcuts starting with a backslash.  Narya does not have its own input mode yet; we recommend the ``TeX`` or ``Agda`` input modes (to be described in a moment).

To select an input-mode, type ``C-\``, enter the name of the input-mode (see below) and hit enter.  You'll have to do this separately in every buffer, but after you've done it once, Emacs remembers the last input-mode you selected so that a single ``C-\`` will toggle that input-mode on and off.  Each input-mode has a one-character indicator that will be displayed in the lower-left corner of the Emacs window when that mode is selected.  If you want to select a different input-mode instead, type ``C-u C-\`` and Emacs will prompt you again for the input-mode name.

- A simple input-mode called ``TeX`` is supplied by default with Emacs, indicated by the character ``\``.  When this mode is enabled, you can use the following shortcuts (and many others):

  * For →, type ``\to`` or ``\rightarrow``
  * For ≔, type ``\coloneq``
  * For ↦, type ``\mapsto``
  * For …, type ``\ldots``

  Note that these particular characters will be automatically converted from their ASCII versions (namely, ``->``, ``:=``, ``|->``, and ``...``) to their Unicode equivalents by Narya's reformatter (assuming ``display chars`` is set to ``unicode``, as it is by default), so it is not necessary to enter them manually.  But you will probably want to enter other Unicode characters at some point as well.

- A fancier input mode called ``Agda`` ships with the proof assistant Agda, indicated by the character ``Π``.  The most convenient way to obtain this mode is to install Agda and its `Emacs mode <https://agda.readthedocs.io/en/latest/getting-started/installation.html#install-agda-mode>`_.  When this mode is enabled, you can use the previously mentioned shortcuts from the ``TeX`` input-mode, and also the following:

  * For →, you can also type ``\r`` (which will also allow you to select from other arrows dynamically).
  * For ≔, you can also type ``\:=``
  * For ℕ, you can type ``\bN``, and similarly for ℤ, ℚ, ℝ, and so on.
  * For superscript characters, you can start with ``\^`` and then the ordinary character, e.g. to get ³ you can type ``\^3``.  This works for numbers, letters, parentheses, and hyphens at least.

  For more information about the Agda input-mode, see the `Agda documentation <https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#unicode-input>`_.  It is also easy to customize by adding to the variable ``agda-input-user-translations``.  Namely, if you type ``M-x customize-variable RET agda-input-user-translations RET``, it will show you a list of user-defined translations (which will start out empty).  You can then click ``INS`` to add a new translation, type the key sequence (without the initial backslash), click ``INS`` underneath it to add the desired unicode character (which you can copy-and-paste from elsewhere, or insert with ``C-x 8 RET`` and then the official unicode character name or hex code).  After repeating this for as many translations as you want, click ``State`` and select ``Save for future sessions``.  For instance, you could define ``\r|`` (entered in the customization as just ``r|``) to insert ↦, and ``\R|`` to insert ⤇.


Unicode fonts
^^^^^^^^^^^^^

By default, Narya uses Unicode characters for many purposes.  Some of these can be turned off, but it is highly recommended that you keep them on and make sure you have sufficient fonts installed to display them.  Traditionally, source code is displayed using a *monospace* font in which all characters have the same width.  Some monospace fonts that are recommended for use with proof assistants that use Unicode characters are `DejaVu Sans Mono <https://dejavu-fonts.github.io/>`_ and `Mononoki <https://madmalik.github.io/mononoki/>`_.

The rest of this section is opinionated and entirely optional.

I find that many Unicode characters with mathematical meaning are difficult to see clearly in a monospace font.  I believe the main argument for a monospace font is so that indentation and vertical alignment can be used to visually structure the code; but this can be achieved with a variable-width font as long as indentations are only ever calculated as constant offsets from the *first* non-space character on a line.  The Narya :ref:`Code formatter` has this property, so I recommend using a variable-width font at least for mathematical Unicode characters.  (A monospace font is fine, and familiar-looking, for ordinary alphanumerics and ASCII symbols.)

Some variable-width fonts containing good-looking mathematical Unicode symbols are:

- `Latin Modern Math <https://www.gust.org.pl/projects/e-foundry/latin-modern>`_.  This is a good default font for most mathematical symbols.
- `Asana Math <https://ctan.org/pkg/asana-math?lang=en>`_.  This is a good choice for a few symbols that are absent or odd-looking in Latin Modern such as √.  I also think it looks better for most letters in other scripts.

It is a little bit tricky to convince Emacs to display different characters in different fonts, and requires adding some custom code to your Emacs configuration file (often called ``.emacs`` in your home directory).  The following instructions are based on personal experiementation; your mileage may vary, and if you have better suggestions please open an issue or pull request.

The magic key is to set ``use-default-font-for-symbols`` to ``nil``.  This instructs Emacs to "honor the fontsets" configured for "symbol" characters, such as mathematical characters, so that it will pay attention if you instruct it to use a different font for these.  (I don't know why this isn't the default; what's the point of allowing you to set the fontset of a character but then ignoring it?)

Now, there are a few characters that are "really" symbols, so that this configuration *should* apply to them; but for some reason Emacs doesn't realize that they are symbols unless you tell it.  This notably includes the first few numerical superscripts ¹ ² ³ (the others are in a different block that Emacs does know are symbols).  Importantly, this must be corrected *before* the magic invocation of ``use-default-font-for-symbols``, e.g. in your ``.emacs`` file:

.. code-block:: none

   (set-char-table-range char-script-table ?¹ 'symbol)
   (set-char-table-range char-script-table ?² 'symbol)
   (set-char-table-range char-script-table ?³ 'symbol)
   (setq use-default-font-for-symbols nil)

In addition, I have found that even after the Latin Modern and Asana fonts are installed system-wide, Emacs doesn't "load" them by default, not even when you add them to a "fontset" (i.e. tell it to use them for certain characters).  The best way I have found to force it to load them is to set them as the default frame font temporarily and then set the default back to what it was before, for instance in the following order in your ``.emacs`` file:

.. code-block:: none

   (set-frame-font "Latin Modern Math")
   (set-frame-font "Asana Math")
   (set-frame-font "DejaVu Sans Mono")

Finally, you need to actually tell Emacs which fonts to use for which characters with ``set-fontset-font``.  This can be passed either a single character such as ``?√`` or a range of characters such as ``(?𝒜 . ?𝒵)``, although when using the latter you need to be aware that, for historical reasons, often a group of characters that would logically fit together in a particular order (such as 𝒜 to 𝒵) may not actually all have consecutive code points.  Here is an example loop from a ``.emacs`` file that configures the font to use for a number of common Unicode symbols:

.. code-block:: none

   (dolist
       (fs '(("Latin Modern Math"
              ;; Use Latin Modern Math for most math characters
              (#x2118 . #x2b4c)
              ?… ?• ?∏
              (?▲ . ?◁)
              ?⟨ ?⟩ ?⟦ ?⟧ ?⟪ ?⟫
              ?′ ?″ ?‴ ?⁗
              )
             ("Asana Math"
              ?√ ?— (?⋲ . ?⋿) (?⦃ . ?⦄)
              ;; Asana is better for most letters (Latin Modern is missing some).
              (#x1d41a . #x1d7cb)
              )
             ("DejaVu Sans"
              ;; Greek letters are in a separate block, and actually look better in DejaVu
              (?Α . ?ϗ)
              )
             ("Latin Modern Math"
              ;; Capital script letters are more readable in Latin Modern.
              ;; 𝒜ℬ𝒞𝒟ℰℱ𝒢ℋℒℳ𝒩𝒪𝒫𝒬ℛ𝒮𝒯𝒰𝒱𝒲𝒳𝒴𝒵
              (?𝒜 . ?𝒵)
              ;; A few script letters are in an earlier block.
              ?ℬ ?ℰ ?ℱ ?ℋ ?ℒ ?ℳ ?ℛ
              ;; Same for double-strucks
              ;; 𝔸𝔹ℂ𝔻𝔼𝔽𝔾ℍ𝕀𝕁𝕂𝕃𝕄ℕ𝕆ℙℚℝ𝕊𝕋𝕌𝕍𝕎𝕏𝕐ℤ
              ;; 𝕒𝕓𝕔𝕕𝕖𝕗𝕘𝕙𝕚𝕛𝕜𝕝𝕞𝕟𝕠𝕡𝕢𝕣𝕤𝕥𝕦𝕧𝕨𝕩𝕪𝕫
              (?𝔸 . ?𝕐)
              ?ℂ ?ℍ ?ℕ ?ℙ ?ℚ ?ℝ ?ℤ ?ℾ ?ℿ ?⅀
              (?𝕒 . ?𝕫)
              ;; Superscript letters ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻ
              ?ᵃ ?ᵇ ?ᶜ ?ᵈ ?ᵉ ?ᶠ ?ᵍ ?ʰ ?ⁱ ?ʲ ?ᵏ ?ˡ ?ᵐ ?ⁿ ?ᵒ ?ᵖ ?ʳ ?ˢ ?ᵗ ?ᵘ ?ᵛ ?ʷ ?ˣ ?ʸ ?ᶻ
              ;; Superscript numbers and math symbols ⁽⁰¹²³⁴⁵⁶⁷⁸⁹⁾⁺⁻⁼
              ?⁰ ?¹ ?² ?³ ?⁴ ?⁵ ?⁶ ?⁷ ?⁸ ?⁹ ?⁽ ?⁾ ?⁺ ?⁻ ?⁼
              ;; Subscript numbers ₀₁₂₃₄₅₆₇₈₉
              ?₀ ?₁ ?₂ ?₃ ?₄ ?₅ ?₆ ?₇ ?₈ ?₉
              ;; Subscript letters (not all exist) ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ
              ?ₐ ?ₑ ?ₕ ?ᵢ ?ⱼ ?ₖ ?ₗ ?ₘ ?ₙ ?ₒ ?ₚ ?ᵣ ?ₛ ?ₜ ?ᵤ ?ᵥ ?ₓ
              )
             ))
     (let ((font (car fs)))
       (dolist (chars (cdr fs))
         (set-fontset-font t chars (font-spec :family font)))))

Some other fonts that are useful for special purposes are `Unifont <https://unifoundry.com/unifont/>`_, which includes many non-mathematical symbols, and `Babelstone <https://www.babelstone.co.uk/Fonts/>`_, which appears to be nearly unique in including the superscript "q" (can your browser display 𐞥?).


For Vim users
^^^^^^^^^^^^^

Unfortunately, there is no analogue of ProofGeneral for Vim.  However, you can install the package `Evil <https://github.com/emacs-evil/evil>`_ to enable Vim-style key commands in Emacs.
