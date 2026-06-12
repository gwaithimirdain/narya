In modal type theory, contexts can contain "locks" which are modalities that change the mode of the context, while environments can contain "keys" that are mode 2-cells whose source is a lock in the codomain (checked length) of the environment and whose target is a lock in the domain (Ctx.t) of the environment.  The function `Env.remove_keys` is supposed to pull off all the keys from an environment whose sources total a given decomposition of the codomain of that environment.  This is used in four places:

1. When evaluating a `Key` term, we remove keys whose sources total the target of that key, compose them, and tack them back on to evaluate the body.

2. Similarly when evaluating a `Key` env.

3. When looking up an index, we remove the keys whose sources total the lock that equals the modal annotation on the variable in order to access the entry behind them.

4. When reading back an `env`, or checking two `env`s for equality, when we encounter a lock sequence in their codomain context, we remove the keys whose sources total that lock sequence, perhaps compare them, and proceed.

We are now generalizing to allow modalities to interact with dimensions.  Each modality can "filter" a dimension, removing some of its generators.  The main point is that a cube of variables, in the domain of a pi-type or in a context, must have a dimension that's filtered by its annotating modality.  But to support this, it appears that adding a key to an environment must also filter the dimension of that environment.  For instance, when evaluating an application of a modal function, the argument is evaluated in a keyed environment and must end up at a filtered dimension to match the domain of the pi-type.

Semantically, a context that is nonparametrically locked has no higher versions (identity/parametricity types).  So there should be no higher-dimensional substitutions with it as codomain.  Thus, when we key an environment, the dimension is filtered by the modality in the *source* of the key (codomain of the substitution).  This is stronger than just filtering by the target, since the source is always at least as nonparametric as the target: we don't currently have exactly that as an assumption, but it's true in the intended models so we can assume it if we need it.

In the intended theories, there are no cells from a parametric modality (one that preserves dimensions when filtering) to a nonparametric one (one that causes nontrivial filtering).  Thus, once there is a lock by a nonparametric modality on a context, all the variables annotated by parametric modalities (such as the identity) are *permanently inaccessible*.  Likewise, therefore, the values in an environment corresponding to such variables in its codomain are also permanently inaccessible, so if necessary we can ignore them or replace them by placeholders (except, perhaps, for readback and equality-checking, if we want to be semantically consistent, since semantically they are *there* and make for different objects and morphisms).

Unfortunately, it seems to be impossible to define `remove_keys` in a way that deals with this filtering and also works at its call sites.  My suggestion is to split up its functionality into multiple functions.

For application (1), and maybe (2), let's do what we need directly: write a function that, rather than removing keys, *replaces* all the keys having a given total source by their horizontal composite, vertically composed with some other cell whose target is that source, producing a new environment directly.  This function can therefore push operator actions, shifts, and unshifts to the *outside* of the key in the new environment, which is the direction that they can be pushed along a filter (with `filter_deg` and so on).  Since the new cell we compose with might have a nonparametric source but a parametric target, the resulting environment could have a more-filtered dimension; but we can make it have the same original dimension by applying a `deg_of_filter` degeneracy outside.

For application (3), I hope we can build key-removal into the `lookup_cube` function, somehow accumulating the operations that should be performed by the intermediate shifts and unshifts in order to apply them all at the end.

Application (4) is beyond scope for the moment, but I hope we can similarly build key-removal into functions like `readback_env` and `equal_env`.
