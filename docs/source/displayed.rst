Displayed type theory
=====================

The combination of flags ``-parametric -arity 1 -direction d -external -discrete-tconn`` is closely related to `displayed type theory <https://arxiv.org/abs/2311.18781>`_ (dTT), and as such can be selected with the single option ``-dtt``.  The primary differences between ``narya -dtt`` and the original dTT of the paper are:

1. Narya has symmetries, which in particular (as noted in the paper) makes ``SST⁽ᵈ⁾`` (see :ref:`Displayed coinductive types`) actually usable.
2. Display (i.e. unary parametricity) in Narya computes only up to isomorphism, and in the case of ``Type`` only up to retract up to isomorphism.
3. (A syntactic difference only) Generic degeneracies in Narya must be parenthesized, so we write ``A⁽ᵈ⁾`` instead of ``Aᵈ``.
4. In Narya's external parametricity, display can only be applied to closed terms, rather than to the more general △□-modal ones as in the paper.

The last difference is more apparent than real, however.  It is possible to access display of any △□-modal type, and any △□-modal term in that type, with the following definitions:

.. code-block:: none

   def disp (X :△□| Type) (x : X) : Type ≔
     ((Y ↦ Y) : ((_ :△□| Type) → Type))⁽ᵈ⁾ X x

   def d (X :△□| Type) (x :△□| X) : disp X x ≔
     ((Y y ↦ y) : ((X :△□| Type) (x :△□| X) → X))⁽ᵈ⁾ X x

Indeed, ``disp X x`` reduces to ``X⁽ᵈ⁾ x``, although the latter is not directly accepted as input syntax.  This can happen because the restrictions imposed by ``-external`` are imposed only at typechecking time: internally, Narya is still happy to compute with degeneracies of arbitrary objects.  In the absence of discrete modalities, the typechecking-time restriction on ``-external`` is (believed to be) sufficient to block all access to display of non-closed terms; but discrete modalities provide an end-run around this.  Fortunately, the access it provides is exactly what is valid semantically and was included syntactically in the paper, namely, that display can be applied to any ``△□``-modal object.
