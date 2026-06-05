open Sface
open Bwsface
open Tface

(* Backwards tube faces *)

type (_, _, _, _) bwtface =
  | LEnd : 'l Endpoints.t * ('m, 'n, 'k, 'nk) bwtface -> ('m, ('n, unit) D.suc, 'k, ('nk, unit) D.suc) bwtface
  | LMid : ('m, 'n, 'k, 'nk) bwtface -> (('m, unit) D.suc, ('n, unit) D.suc, 'k, ('nk, unit) D.suc) bwtface
  | REnd : 'l Endpoints.t * ('m, 'k) bwsface -> ('m, D.zero, ('k, unit) D.suc, ('k, unit) D.suc) bwtface
  | RMid : ('m, D.zero, 'k, 'k) bwtface -> (('m, unit) D.suc, D.zero, ('k, unit) D.suc, ('k, unit) D.suc) bwtface

let rec dom_bwtface : type m n k nk. (m, n, k, nk) bwtface -> m D.t = function
  | LEnd (_, d) -> dom_bwtface d
  | LMid d -> D.suc (dom_bwtface d) Unit
  | REnd (_, d) -> dom_bwsface d
  | RMid d -> D.suc (dom_bwtface d) Unit

let rec codl_bwtface : type m n k nk. (m, n, k, nk) bwtface -> n D.t = function
  | LEnd (_, d) -> D.suc (codl_bwtface d) Unit
  | LMid d -> D.suc (codl_bwtface d) Unit
  | REnd (_, _) -> D.zero
  | RMid _ -> D.zero

(*
let rec codr_bwtface : type m n k nk. (m, n, k, nk) bwtface -> k D.t = function
  | LEnd (_, d) -> codr_bwtface d
  | LMid d -> codr_bwtface d
  | REnd (_, d) -> D.suc (cod_bwsface d) Unit
  | RMid d -> D.suc (codr_bwtface d) Unit
*)

let rec cod_bwtface : type m n k nk. (m, n, k, nk) bwtface -> nk D.t = function
  | LEnd (_, d) -> D.suc (cod_bwtface d) Unit
  | LMid d -> D.suc (cod_bwtface d) Unit
  | REnd (_, d) -> D.suc (cod_bwsface d) Unit
  | RMid d -> D.suc (cod_bwtface d) Unit

let rec bwsface_of_bwtface : type m n k nk. (m, n, k, nk) bwtface -> (m, nk) bwsface = function
  | LEnd (e, d) -> End (D.deg, e, bwsface_of_bwtface d)
  | LMid d -> Mid (D.deg, bwsface_of_bwtface d)
  | REnd (e, d) -> End (D.deg, e, d)
  | RMid d -> Mid (D.deg, bwsface_of_bwtface d)

let bwtface_rend : type l m k.
    l Endpoints.t -> (m, D.zero, k, k) bwtface -> (m, D.zero, (k, unit) D.suc, (k, unit) D.suc) bwtface =
 fun e d -> REnd (e, bwsface_of_bwtface d)

(* Converting a backwards tube face to a forwards one.  This requires three helper functions. *)

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
  | End (g, e, bf) -> (
      (* TODO: bridge via G.compare; will be removed once tface_of_bw_r uses word.ml structured forms instead of D.suc_plus. *)
      match D.G.compare g D.deg with
      | Neq -> assert false
      | Eq -> tface_of_bw_r m12 (D.suc_plus k12) (D.suc_plus nk12) (tface_end f e) bf)
  | Mid (g, bf) -> (
      match D.G.compare g D.deg with
      | Neq -> assert false
      | Eq ->
          tface_of_bw_r (D.suc_plus m12) (D.suc_plus k12) (D.suc_plus nk12) (Mid (f, D.deg)) bf)

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
  | REnd (e, bf) ->
      tface_of_bw_r m12 (D.suc_plus k12) (D.suc_plus n12k) (End (f, nk12, D.deg, e)) bf
  | RMid bf ->
      tface_of_bw_lt (D.suc_plus m12) (D.suc_plus k12) (D.suc_plus n12k) (Suc (nk12, Unit))
        (Mid (f, D.deg)) bf

let rec tface_of_bw_ls : type m1 m2 m n1 n2 k n nk nk2.
    (m1, m2, m) D.plus ->
    (n1, n2, n) D.plus ->
    (n1, nk2, nk) D.plus ->
    (m1, n1) sface ->
    (m2, n2, k, nk2) bwtface ->
    (m, n, k, nk) tface =
 fun m12 n12 nk12 f bf ->
  match bf with
  | LEnd (e, bf) ->
      tface_of_bw_ls m12 (D.suc_plus n12) (D.suc_plus nk12) (End (f, D.deg, e)) bf
  | LMid bf ->
      tface_of_bw_ls (D.suc_plus m12) (D.suc_plus n12) (D.suc_plus nk12) (Mid (f, D.deg)) bf
  | REnd (e, bf) ->
      let n1 = cod_sface f in
      let Eq = D.plus_uniq n12 (D.plus_zero n1) in
      tface_of_bw_r m12
        (D.suc_plus_eq_suc (D.zero_plus (cod_bwsface bf)))
        (D.suc_plus nk12)
        (End (f, D.plus_zero n1, D.deg, e))
        bf
  | RMid bf ->
      let n1 = cod_sface f in
      let Eq = D.plus_uniq n12 (D.plus_zero n1) in
      tface_of_bw_lt (D.suc_plus m12)
        (D.suc_plus_eq_suc (D.zero_plus (cod_bwtface bf)))
        (D.suc_plus nk12) (Suc (Zero, Unit)) (Mid (f, D.deg)) bf

let tface_of_bw : type m n k nk. (m, n, k, nk) bwtface -> (m, n, k, nk) tface =
 fun bf ->
  tface_of_bw_ls
    (D.zero_plus (dom_bwtface bf))
    (D.zero_plus (codl_bwtface bf))
    (D.zero_plus (cod_bwtface bf))
    (id_sface D.zero) bf
