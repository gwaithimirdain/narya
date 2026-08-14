open Term

(* Whether strict parametric discreteness is on globally.  This is part of the type theory options (see Options), which are fixed once, before any code is checked, and never change thereafter.  It is a plain reference rather than a reader effect because the options aren't known until the leading "option" commands of the first file have been executed, by which time we are already inside the handlers that would have had to wrap it. *)
let state = ref false
let enabled () = !state
let set b = state := b

(* Given a case tree definition, check whether it could be discrete, which means it's an abstracted datatype with all parameters/indices/constructor arguments discrete or currently being defined.  Return a version of it with discrete turned on for sure if possible, and a boolean indicating whether it could be discrete.  *)
let rec discrete_def : type mode b. (mode, b, potential) term -> (mode, b, potential) term * bool =
  function
  | Lam (x, p, filter, body) ->
      let t, d = discrete_def body in
      (Lam (x, p, filter, t), d)
  | Canonical (Data { indices; constrs; discrete = `Maybe; recursive; hints; tyfam }) ->
      (Canonical (Data { indices; constrs; discrete = `Yes; recursive; hints; tyfam }), true)
  | tm -> (tm, false)
