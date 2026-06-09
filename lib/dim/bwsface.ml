open Sface

(* "Backwards strict faces" contain the same data as ordinary strict faces, but are inductive on the other side, like lists and backward lists. *)

type (_, _) bwsface =
  | Zero : (D.zero, D.zero) bwsface
  | End :
      'g D.G.t * 'l Endpoints.t * ('m, 'n) bwsface
      -> ('m, ('n, 'g) D.suc) bwsface
  | Mid :
      'g D.G.t * ('m, 'n) bwsface
      -> (('m, 'g) D.suc, ('n, 'g) D.suc) bwsface

let rec dom_bwsface : type m n. (m, n) bwsface -> m D.t = function
  | Zero -> Word Zero
  | End (_, _, f) ->
      let (Word s) = dom_bwsface f in
      Word s
  | Mid (g, f) ->
      let (Word s) = dom_bwsface f in
      Word (Suc (s, g))

let rec cod_bwsface : type m n. (m, n) bwsface -> n D.t = function
  | Zero -> Word Zero
  | End (g, _, f) ->
      let (Word s) = cod_bwsface f in
      Word (Suc (s, g))
  | Mid (g, f) ->
      let (Word s) = cod_bwsface f in
      Word (Suc (s, g))

(* Push an End onto the innermost end of an sface.  Single-direction-only: relies on the [let Unit = g_outer] refinement that lets the codom's two outermost generators commute in the type system.  Replaces the original sface_of_bw_onto accumulator's D.suc_plus rightmost-shift. *)
let rec push_end_at_inner : type m n l.
    (m, n) sface -> unit D.G.t -> l Endpoints.t -> (m, (n, unit) D.suc) sface =
 fun f g e ->
  match f with
  | Zero -> End (Zero, g, e)
  | End (f_inner, g_outer, e_outer) ->
      let Unit = g_outer in
      End (push_end_at_inner f_inner g e, g_outer, e_outer)
  | Mid (f_inner, g_outer) ->
      let Unit = g_outer in
      Mid (push_end_at_inner f_inner g e, g_outer)

(* Push a Mid onto the innermost end of an sface.  Single-direction-only. *)
let rec push_mid_at_inner : type m n.
    (m, n) sface -> unit D.G.t -> ((m, unit) D.suc, (n, unit) D.suc) sface =
 fun f g ->
  match f with
  | Zero -> Mid (Zero, g)
  | End (f_inner, g_outer, e_outer) ->
      let Unit = g_outer in
      End (push_mid_at_inner f_inner g, g_outer, e_outer)
  | Mid (f_inner, g_outer) ->
      let Unit = g_outer in
      Mid (push_mid_at_inner f_inner g, g_outer)

(* Convert a bwsface to its sface.  Recurses inner-first, then pushes each level's End/Mid at the innermost of the accumulating sface; this achieves the orientation flip (bwsface outer-End → sface inner-End) without D.suc_plus.  Single-direction-only. *)
let rec sface_of_bw : type m n. (m, n) bwsface -> (m, n) sface = function
  | Zero -> Zero
  | End (g, e, bf) ->
      let Unit = g in
      let f = sface_of_bw bf in
      push_end_at_inner f g e
  | Mid (g, bf) ->
      let Unit = g in
      let f = sface_of_bw bf in
      push_mid_at_inner f g
