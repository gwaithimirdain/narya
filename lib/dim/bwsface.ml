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

(* Phase 7 redesign: bwsface_v2 carries an insertion witness in each Mid/End constructor saying WHERE the new generator goes in the codom.  In single-direction (current), the insertion is always Now (rightmost), but this lets sface_of_bw use it to place each generator at the correct sface position without needing D.suc_plus's rightmost shift.  In multi-direction, the cube descent will compute the correct insertion. *)

type (_, _) bwsface_v2 =
  | Zero : (D.zero, D.zero) bwsface_v2
  | End :
      'g D.G.t * 'l Endpoints.t * ('m, 'n_inner) bwsface_v2 * ('n_inner, 'g, 'n) D.insert
      -> ('m, 'n) bwsface_v2
  | Mid :
      'g D.G.t * ('m_inner, 'n_inner) bwsface_v2
      * ('n_inner, 'g, 'n) D.insert * ('m_inner, 'g, 'm) D.insert
      -> ('m, 'n) bwsface_v2

(* Walk into an sface and add an End at the position indicated by the insertion. *)
let rec insert_end_in_sface : type m n g n_new l.
    (m, n) sface -> g D.G.t -> l Endpoints.t -> (n, g, n_new) D.insert -> (m, n_new) sface =
 fun f g e ins ->
  match ins with
  | Now -> End (f, g, e)
  | Later ins_inner -> (
      match f with
      | End (f_inner, g_outer, e_outer) ->
          End (insert_end_in_sface f_inner g e ins_inner, g_outer, e_outer)
      | Mid (f_inner, g_outer) ->
          Mid (insert_end_in_sface f_inner g e ins_inner, g_outer))

(* Walk into an sface and add a Mid at the position indicated by the dual insertions on dom and codom.  For an End-constructor along the path, only the codom insertion advances (dom isn't touched by End); for a Mid-constructor, both advance together.

   The caller must ensure ins_n and ins_m are consistent — the new Mid is at the SAME relative depth in both dom and codom.  Inconsistent pairings (e.g., codom-outer + dom-deep) are impossible for a well-formed Mid and reach the assert false. *)
let rec insert_mid_in_sface : type m n g m_new n_new.
    (m, n) sface -> g D.G.t -> (n, g, n_new) D.insert -> (m, g, m_new) D.insert -> (m_new, n_new) sface =
 fun f g ins_n ins_m ->
  match ins_n with
  | Now -> (
      match ins_m with
      | Now -> Mid (f, g)
      | Later _ -> assert false)
  | Later ins_n_inner -> (
      match f with
      | End (f_inner, g_outer, e_outer) ->
          End (insert_mid_in_sface f_inner g ins_n_inner ins_m, g_outer, e_outer)
      | Mid (f_inner, g_outer) -> (
          match ins_m with
          | Later ins_m_inner ->
              Mid (insert_mid_in_sface f_inner g ins_n_inner ins_m_inner, g_outer)
          | Now -> assert false))

(* New sface_of_bw: walks the bwsface_v2 recursively, using each constructor's insertion to place its generator at the right position in the result sface.  No D.suc_plus. *)
let rec sface_of_bw_v2 : type m n. (m, n) bwsface_v2 -> (m, n) sface = function
  | Zero -> Zero
  | End (g, e, bf, ins) ->
      let f = sface_of_bw_v2 bf in
      insert_end_in_sface f g e ins
  | Mid (g, bf, ins_n, ins_m) ->
      let f = sface_of_bw_v2 bf in
      insert_mid_in_sface f g ins_n ins_m

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
