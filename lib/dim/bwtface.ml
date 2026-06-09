open Sface
open Bwsface
open Tface

(* Backwards tube faces *)

type (_, _, _, _) bwtface =
  | LEnd :
      'g D.G.t * 'l Endpoints.t * ('m, 'n, 'k, 'nk) bwtface
      -> ('m, ('n, 'g) D.suc, 'k, ('nk, 'g) D.suc) bwtface
  | LMid :
      'g D.G.t * ('m, 'n, 'k, 'nk) bwtface
      -> (('m, 'g) D.suc, ('n, 'g) D.suc, 'k, ('nk, 'g) D.suc) bwtface
  | REnd :
      'g D.G.t * 'l Endpoints.t * ('m, 'k) bwsface
      -> ('m, D.zero, ('k, 'g) D.suc, ('k, 'g) D.suc) bwtface
  | RMid :
      'g D.G.t * ('m, D.zero, 'k, 'k) bwtface
      -> (('m, 'g) D.suc, D.zero, ('k, 'g) D.suc, ('k, 'g) D.suc) bwtface

let rec dom_bwtface : type m n k nk. (m, n, k, nk) bwtface -> m D.t = function
  | LEnd (_, _, d) -> dom_bwtface d
  | LMid (g, d) -> D.suc (dom_bwtface d) g
  | REnd (_, _, d) -> dom_bwsface d
  | RMid (g, d) -> D.suc (dom_bwtface d) g

let rec codl_bwtface : type m n k nk. (m, n, k, nk) bwtface -> n D.t = function
  | LEnd (g, _, d) -> D.suc (codl_bwtface d) g
  | LMid (g, d) -> D.suc (codl_bwtface d) g
  | REnd (_, _, _) -> D.zero
  | RMid _ -> D.zero

(*
let rec codr_bwtface : type m n k nk. (m, n, k, nk) bwtface -> k D.t = function
  | LEnd (_, _, d) -> codr_bwtface d
  | LMid (_, d) -> codr_bwtface d
  | REnd (g, _, d) -> D.suc (cod_bwsface d) g
  | RMid (g, d) -> D.suc (codr_bwtface d) g
*)

let rec cod_bwtface : type m n k nk. (m, n, k, nk) bwtface -> nk D.t = function
  | LEnd (g, _, d) -> D.suc (cod_bwtface d) g
  | LMid (g, d) -> D.suc (cod_bwtface d) g
  | REnd (g, _, d) -> D.suc (cod_bwsface d) g
  | RMid (g, d) -> D.suc (cod_bwtface d) g

let rec bwsface_of_bwtface : type m n k nk. (m, n, k, nk) bwtface -> (m, nk) bwsface = function
  | LEnd (g, e, d) -> End (g, e, bwsface_of_bwtface d)
  | LMid (g, d) -> Mid (g, bwsface_of_bwtface d)
  | REnd (g, e, d) -> End (g, e, d)
  | RMid (g, d) -> Mid (g, bwsface_of_bwtface d)

let bwtface_rend : type l m k.
    l Endpoints.t -> (m, D.zero, k, k) bwtface -> (m, D.zero, (k, unit) D.suc, (k, unit) D.suc) bwtface =
 fun e d -> REnd (D.deg, e, bwsface_of_bwtface d)

(* Converting a backwards tube face to a forwards one.  This requires three helper functions.

   Phase 7: D.suc_plus_eq_suc and D.suc_plus are replaced by LOCAL helpers (push_unit_left and local_suc_plus below) that do the same recursive transformation but without depending on D.ml's commutativity-dependent functions.  Single-direction only — the helpers use [Suc (_, Unit)] patterns that require g = unit. *)

(* Add unit on the LEFT side of a plus relation: (a, b, c) plus → ((a, unit) suc, b, (c, unit) suc) plus.  Local replacement for D.suc_plus_eq_suc. *)
let rec push_unit_left : type a b c.
    (a, b, c) D.plus -> ((a, unit) D.suc, b, (c, unit) D.suc) D.plus = function
  | Zero -> Zero
  | Suc (p, Unit) -> Suc (push_unit_left p, Unit)

(* Shift a unit from the middle to the left: (m, (n, unit) suc, p) plus → ((m, unit) suc, n, p) plus.  Local replacement for D.suc_plus. *)
let local_suc_plus : type m n p.
    (m, (n, unit) D.suc, p) D.plus -> ((m, unit) D.suc, n, p) D.plus =
 fun x ->
  let (Suc (y, Unit)) = push_unit_left x in
  y

let rec tface_of_bw_r : type m1 m2 m n k1 k2 k nk1 nk.
    (m1, m2, m) D.plus ->
    (k1, k2, k) D.plus ->
    (nk1, k2, nk) D.plus ->
    (m1, n, k1, nk1) tface ->
    (m2, k2) bwsface ->
    (m, n, k, nk) tface =
 fun m12 k12 nk12 f bf ->
  match bf with
  | Zero ->
      let m1, k1, nk1 = (dom_tface f, codr_tface f, cod_tface f) in
      let Eq = D.plus_uniq m12 (D.plus_zero m1) in
      let Eq = D.plus_uniq k12 (D.plus_zero k1) in
      let Eq = D.plus_uniq nk12 (D.plus_zero nk1) in
      f
  | End (g, e, bf) ->
      let Unit = g in
      tface_of_bw_r m12 (local_suc_plus k12) (local_suc_plus nk12) (tface_end f e) bf
  | Mid (g, bf) ->
      let Unit = g in
      tface_of_bw_r (local_suc_plus m12) (local_suc_plus k12) (local_suc_plus nk12) (Mid (f, D.deg)) bf

let rec tface_of_bw_lt : type m1 m2 m n k1 k2 k nk nk1.
    (m1, m2, m) D.plus ->
    (k1, k2, k) D.plus ->
    (nk1, k2, nk) D.plus ->
    (n, k1, nk1) D.plus ->
    (m1, nk1) sface ->
    (m2, D.zero, k2, k2) bwtface ->
    (m, n, k, nk) tface =
 fun m12 k12 n12k nk12 f bf ->
  match bf with
  | REnd (g, e, bf) ->
      let Unit = g in
      tface_of_bw_r m12 (local_suc_plus k12) (local_suc_plus n12k) (End (f, nk12, g, e)) bf
  | RMid (g, bf) ->
      let Unit = g in
      tface_of_bw_lt (local_suc_plus m12) (local_suc_plus k12) (local_suc_plus n12k) (Suc (nk12, Unit))
        (Mid (f, g)) bf

let rec tface_of_bw_ls : type m1 m2 m n1 n2 k n nk nk2.
    (m1, m2, m) D.plus ->
    (n1, n2, n) D.plus ->
    (n1, nk2, nk) D.plus ->
    (m1, n1) sface ->
    (m2, n2, k, nk2) bwtface ->
    (m, n, k, nk) tface =
 fun m12 n12 nk12 f bf ->
  match bf with
  | LEnd (g, e, bf) ->
      let Unit = g in
      tface_of_bw_ls m12 (local_suc_plus n12) (local_suc_plus nk12) (End (f, g, e)) bf
  | LMid (g, bf) ->
      let Unit = g in
      tface_of_bw_ls (local_suc_plus m12) (local_suc_plus n12) (local_suc_plus nk12) (Mid (f, g)) bf
  | REnd (g, e, bf) ->
      let Unit = g in
      let n1 = cod_sface f in
      let Eq = D.plus_uniq n12 (D.plus_zero n1) in
      tface_of_bw_r m12
        (push_unit_left (D.zero_plus (cod_bwsface bf)))
        (local_suc_plus nk12)
        (End (f, D.plus_zero n1, g, e))
        bf
  | RMid (g, bf) ->
      let Unit = g in
      let n1 = cod_sface f in
      let Eq = D.plus_uniq n12 (D.plus_zero n1) in
      tface_of_bw_lt (local_suc_plus m12)
        (push_unit_left (D.zero_plus (cod_bwtface bf)))
        (local_suc_plus nk12) (Suc (Zero, Unit)) (Mid (f, g)) bf

let tface_of_bw : type m n k nk. (m, n, k, nk) bwtface -> (m, n, k, nk) tface =
 fun bf ->
  tface_of_bw_ls
    (D.zero_plus (dom_bwtface bf))
    (D.zero_plus (codl_bwtface bf))
    (D.zero_plus (cod_bwtface bf))
    (id_sface D.zero) bf
