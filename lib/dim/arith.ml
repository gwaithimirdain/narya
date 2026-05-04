open Util

(* Since dimensions are epimorphisms, given n and nk there is at most one k such that (n,k,nk) D.plus.  This function finds it if it exists. *)

type (_, _) factor = Factor : ('n, 'k, 'nk) D.plus -> ('nk, 'n) factor

let rec factor : type nk n. nk D.t -> n D.t -> (nk, n) factor option =
 fun nk n ->
  let open Monad.Ops (Monad.Maybe) in
  match D.compare nk n with
  | Eq -> Some (Factor Zero)
  | Neq -> (
      match nk with
      | Word Zero -> None
      | Word (Suc (nk, Unit)) ->
          let* (Factor n_k) = factor (Word nk) n in
          return (Factor (Suc (n_k, Unit))))

type (_, _) cofactor = Cofactor : ('n, 'k, 'nk) D.plus -> ('nk, 'k) cofactor

let rec cofactor : type nk k. nk D.t -> k D.t -> (nk, k) cofactor option =
 fun nk k ->
  let open Monad.Ops (Monad.Maybe) in
  match (nk, k) with
  | Word Zero, Word Zero -> Some (Cofactor Zero)
  | Word (Suc (nk, Unit)), Word (Suc (k, Unit)) ->
      let* (Cofactor n) = cofactor (Word nk) (Word k) in
      return (Cofactor (Suc (n, Unit)))
  | Word (Suc _), Word Zero -> return (Cofactor (D.plus_zero nk))
  | _ -> None

(* Compute the pushout of a span of dimensions, if it exists. *)

type (_, _) pushout = Pushout : ('a, 'c, 'p) D.plus * ('b, 'd, 'p) D.plus -> ('a, 'b) pushout

let pushout : type a b. a D.t -> b D.t -> (a, b) pushout =
 fun a b ->
  match (factor a b, factor b a) with
  | _, Some (Factor ab) -> Pushout (ab, Zero)
  | Some (Factor ba), _ -> Pushout (Zero, ba)
  | _ -> raise (Failure "Dim.pushout")

(* A dimension is totally nullary if all its directions have arity zero.  Currently there is only one direction, so it suffices to test whether the overall arity is zero.  *)

let totally_nullary : type a. a D.t -> bool =
 fun _ ->
  let (Wrap l) = Endpoints.wrapped () in
  match Endpoints.len l with
  | N.Nat Zero -> true
  | N.Nat (Suc _) -> false
