# Narya: A proof assistant for higher-dimensional type theory

Narya is eventually intended to be a proof assistant implementing Multi-Modal, Multi-Directional, Higher/Parametric/Displayed Observational Type Theory, but a formal type theory combining all those adjectives has not yet been specified.  At the moment, Narya implements a normalization-by-evaluation algorithm and typechecker for an observational-style theory with Id/Bridge types satisfying parametricity, of variable arity and internality.  There is a parser with user-definable mixfix notations, and user-definable record types, inductive datatypes and type families, and coinductive codatatypes, with functions definable by matching and comatching case trees, import and export and separate compilation, the ability to leave holes and solve them later, and a ProofGeneral interaction mode.

Narya is very much a work in progress.  Expect breaking changes, including even in fundamental aspects of the syntax.  (I try to make breaking changes as GitHub pull requests, so if you watch the repository you should at least get notified of them.)  But on the other side of the coin, feedback on anything and everything is welcome.  In particular, please report all crashes, bugs, unexpected errors, and other unexpected, surprising, or unintuitive behavior, either in GitHub issues or by direct email.


## Links

- [Installation](https://gwaithimirdain.github.io/narya/installation.html)
- [Documentation](https://gwaithimirdain.github.io/narya/)
- [Contributing to Narya](https://gwaithimirdain.github.io/narya/contributing.html)

