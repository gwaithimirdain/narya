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

(* TODO: bwsface's outer-End convention corresponds to sface's inner-End position; preserving this in multi-generator code requires more than a simple recursive rewrite.  For now, keep the accumulator-based algorithm with [D.suc_plus]; restructuring it to be commutativity-free is a Phase 5+ task. *)
let sface_of_bw : type m n. (m, n) bwsface -> (m, n) sface =
 fun bf ->
  let rec sface_of_bw_onto : type k l m n km ln.
      (k, m, km) D.plus ->
      (l, n, ln) D.plus ->
      (k, l) sface ->
      (m, n) bwsface ->
      (km, ln) sface =
   fun km ln f bf ->
    match bf with
    | Zero ->
        let Zero, Zero = (km, ln) in
        f
    | End (g, e, bf) -> (
        (* TODO: bridge via G.compare; in single-generator this Eq always holds. *)
        match D.G.compare g D.deg with
        | Neq -> assert false
        | Eq -> sface_of_bw_onto km (D.suc_plus ln) (End (f, g, e)) bf)
    | Mid (g, bf) -> (
        match D.G.compare g D.deg with
        | Neq -> assert false
        | Eq ->
            sface_of_bw_onto (D.suc_plus km) (D.suc_plus ln) (Mid (f, g)) bf) in
  sface_of_bw_onto
    (D.zero_plus (dom_bwsface bf))
    (D.zero_plus (cod_bwsface bf))
    (id_sface D.zero) bf
