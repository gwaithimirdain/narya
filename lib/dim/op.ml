open Util
open Signatures
open Deg
open Sface

(* If m and n are dimensions, (m,n) op is the type of dimensional operators m => n, which act on types and terms contravariantly.  We define these in an intrinsically correct way, using a strict factorization system consisting of degeneracies and strict faces.  *)

(* A generalized operator allows generalized strict faces. *)

module GOp (E : Fam) = struct
  module F = GSFace (E)

  type (_, _) op = Op : ('n, 'k) F.sface * ('m, 'n) deg -> ('m, 'k) op

  let id_op : type n. n D.t -> (n, n) op = fun n -> Op (F.id_sface n, id_deg n)

  (* To compose operators, we use another distributive law. *)

  let rec deg_sface : type m n k. (n, k) deg -> (m, n) F.sface -> (m, k) op =
   fun a b ->
    match a with
    | Zero _ ->
        let m = F.dom_sface b in
        Op (Zero, Zero m)
    | Suc (p, k) -> (
        match F.sface_residual b k with
        | Residual_End (f, e) ->
            let (Op (f', p')) = deg_sface p f in
            Op (End (f', e), p')
        | Residual_Mid (f, l) ->
            let (Op (f', p')) = deg_sface p f in
            Op (Mid f', Suc (p', l)))

  let dom_op : type m n. (m, n) op -> m D.t = function
    | Op (_, s) -> dom_deg s

  let comp_op : type m n k. (n, k) op -> (m, n) op -> (m, k) op =
   fun (Op (a, b)) (Op (c, d)) ->
    let (Op (c', b')) = deg_sface b c in
    Op (F.comp_sface a c', comp_deg b' d)

  let is_id_op : type m n. (m, n) op -> (m, n) Eq.t option =
   fun (Op (a, b)) ->
    match (F.is_id_sface a, is_id_deg b) with
    | Some Eq, Some Eq -> Some Eq
    | _ -> None

  let op_plus_op : type m n mn k l kl.
      (k, m) op -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) op -> (kl, mn) op =
   fun (Op (d1, s1)) mn kl (Op (d2, s2)) ->
    let (Plus middle) = D.plus (F.dom_sface d2) in
    Op (F.sface_plus_sface d1 mn middle d2, deg_plus_deg s1 middle kl s2)

  let plus_op : type m n mn l ml.
      m D.t -> (m, n, mn) D.plus -> (m, l, ml) D.plus -> (l, n) op -> (ml, mn) op =
   fun m mn ml op -> op_plus_op (id_op m) mn ml op

  let op_plus : type m n mn k kn. (k, m) op -> (m, n, mn) D.plus -> (k, n, kn) D.plus -> (kn, mn) op
      =
   fun op mn kn -> op_plus_op op mn kn (id_op (D.plus_right mn))
end

include GOp (Endpoints)
module Opt = GOp (OptEndpoints)

type ('a, 'b) opt_op = ('a, 'b) Opt.op

let id_opt_op = Opt.id_op
let comp_opt_op = Opt.comp_op
let dom_opt_op = Opt.dom_op
let is_id_opt_op = Opt.is_id_op

let op_of_opt : type a b. (a, b) opt_op -> (a, b) op option = function
  | Op (f, s) -> (
      match sface_of_opt f with
      | None -> None
      | Some f -> Some (Op (f, s)))

let opt_of_op : type a b. (a, b) op -> (a, b) opt_op = fun (Op (f, s)) -> Op (opt_of_sface f, s)

let cod_op : type m n. (m, n) op -> n D.t = function
  | Op (f, _) -> cod_sface f

let op_of_deg : type m n. (m, n) deg -> (m, n) op = fun s -> Op (id_sface (cod_deg s), s)

let opt_op_of_deg : type m n. (m, n) deg -> (m, n) opt_op =
 fun s -> Op (Sface.Opt.id_sface (cod_deg s), s)

let op_of_sface : type m n. (m, n) sface -> (m, n) op = fun f -> Op (f, id_deg (dom_sface f))

let opt_op_of_sface : type m n. (m, n) sface -> (m, n) opt_op =
 fun f -> Op (opt_of_sface f, id_deg (dom_sface f))

let opt_op_of_opt_sface : type m n. (m, n) opt_sface -> (m, n) opt_op =
 fun f -> Op (f, id_deg (Sface.Opt.dom_sface f))

let plus_opt_op : type m n mn l ml.
    m D.t -> (m, n, mn) D.plus -> (m, l, ml) D.plus -> (l, n) opt_op -> (ml, mn) opt_op =
 fun m mn ml o -> Opt.plus_op m mn ml o

let opt_op_plus : type m n mn k kn.
    (k, m) opt_op -> (m, n, mn) D.plus -> (k, n, kn) D.plus -> (kn, mn) opt_op =
 fun o mn kn -> Opt.op_plus o mn kn

type _ op_of = Of : ('m, 'n) op -> 'n op_of
type _ op_of_plus = Of : ('m, 'n) sface * 'm deg_of_plus -> 'n op_of_plus

let comp_op_of : type m n. (m, n) op -> m op_of -> n op_of = fun op (Of op') -> Of (comp_op op op')

let comp_op_deg_of_plus : type m n. (m, n) op -> m deg_of_plus -> n op_of_plus =
 fun (Op (f, s2)) s1 -> Of (f, comp_deg_of_plus s2 s1)
