Displayed type theory
=====================

The combination of flags ``-parametric -arity 1 -direction d -external -discrete-tconn`` is closely related to `displayed type theory <https://arxiv.org/abs/2311.18781>`_ (dTT), and as such can be selected with the single option ``-dtt``.  The primary differences between ``narya -dtt`` and the original dTT of the paper are:

1. Narya has symmetries, which in particular (as noted in the paper) seems to be required for many things, including working with ``SST⁽ᵈ⁾`` (see :ref:`Displayed coinductive types`).
2. Display (i.e. unary parametricity) in Narya computes only up to isomorphism, and in the case of ``Type`` only up to retract up to isomorphism, whereas in the dTT paper it computes definitionally.
3. (A syntactic difference only) Generic degeneracies in Narya must be parenthesized, so we write ``A⁽ᵈ⁾`` instead of ``Aᵈ``.
