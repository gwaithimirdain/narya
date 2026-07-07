open Util
open Signatures
open Singleton

(* ********** Strict faces ********** *)

(* A strict face is an order-preserving partial map that is surjective and with an endpoint index assigned to each element not mapping to the codomain. A generalized strict face allows alternative notions of "endpoint".  *)

module GSFace (E : Fam) = struct
  type (_, _) sface =
    | Zero : (D.zero, D.zero) sface
    | End : ('m, 'n) sface * 'l E.t -> ('m, 'n D.suc) sface
    | Mid : ('m, 'n) sface -> ('m D.suc, 'n D.suc) sface

  let rec id_sface : type n. n D.t -> (n, n) sface = function
    | Word Zero -> Zero
    | Word (Suc (n, Unit)) -> Mid (id_sface (Word n))

  let rec dom_sface : type m n. (m, n) sface -> m D.t = function
    | Zero -> Word Zero
    | End (f, _) ->
        let (Word s) = dom_sface f in
        Word s
    | Mid f ->
        let (Word s) = dom_sface f in
        Word (Suc (s, Unit))

  let rec comp_sface : type m n k. (n, k) sface -> (m, n) sface -> (m, k) sface =
   fun a b ->
    match (a, b) with
    | Zero, Zero -> Zero
    | End (a', e), _ -> End (comp_sface a' b, e)
    | Mid a', End (b', e) -> End (comp_sface a' b', e)
    | Mid a', Mid b' -> Mid (comp_sface a' b')

  (* A "residual" of a strict face and an index picks out the image of that index and the strict face with that index and its image (if any) removed.  This is used to compose non-strict faces and operators. *)

  type (_, _) sface_residual =
    | Residual_End : ('m, 'n) sface * 'l E.t -> ('m, 'n) sface_residual
    | Residual_Mid : ('m, 'n) sface * ('m, 'msuc) D.insert -> ('msuc, 'n) sface_residual

  let rec sface_residual : type m n npred.
      (m, n) sface -> (npred, n) D.insert -> (m, npred) sface_residual =
   fun f k ->
    match (k, f) with
    | Now, End (f', e) -> Residual_End (f', e)
    | Now, Mid f' -> Residual_Mid (f', Now)
    | Later k', End (f', e) -> (
        match sface_residual f' k' with
        | Residual_End (f'', e') -> Residual_End (End (f'', e), e')
        | Residual_Mid (f'', l) -> Residual_Mid (End (f'', e), l))
    | Later k', Mid f' -> (
        match sface_residual f' k' with
        | Residual_End (f'', e') -> Residual_End (Mid f'', e')
        | Residual_Mid (f'', l) -> Residual_Mid (Mid f'', Later l))

  let rec is_id_sface : type m n. (m, n) sface -> (m, n) Eq.t option = function
    | Zero -> Some Eq
    | End _ -> None
    | Mid f -> (
        match is_id_sface f with
        | Some Eq -> Some Eq
        | None -> None)

  (* Concatenate two strict faces left-to-right. *)
  let rec sface_plus_sface : type m n mn k p kp.
      (k, m) sface -> (m, n, mn) D.plus -> (k, p, kp) D.plus -> (p, n) sface -> (kp, mn) sface =
   fun fkm mn kp fpn ->
    match (fpn, mn, kp) with
    | Zero, Zero, Zero -> fkm
    | End (fpn, e), Suc (mn, Unit), kp -> End (sface_plus_sface fkm mn kp fpn, e)
    | Mid fpn, Suc (mn, Unit), Suc (kp, Unit) -> Mid (sface_plus_sface fkm mn kp fpn)

  (* In particular, we can extend by identities on the right or left. *)

  let sface_plus : type m n mn k kn.
      (k, m) sface -> (m, n, mn) D.plus -> (k, n, kn) D.plus -> (kn, mn) sface =
   fun f mn kn -> sface_plus_sface f mn kn (id_sface (D.plus_right mn))

  let plus_sface : type m n nm k nk.
      n D.t -> (n, m, nm) D.plus -> (n, k, nk) D.plus -> (k, m) sface -> (nk, nm) sface =
   fun n nm nk f -> sface_plus_sface (id_sface n) nm nk f
end

include GSFace (Endpoints)

(* An optional sface allows "missing" endpoints. *)
module OptEndpoints = struct
  type 'l t = 'l Endpoints.t option
end

module Opt = GSFace (OptEndpoints)

type ('a, 'b) opt_sface = ('a, 'b) Opt.sface

let rec sface_of_opt : type a b. (a, b) opt_sface -> (a, b) sface option =
 fun f ->
  let open Monad.Ops (Monad.Maybe) in
  match f with
  | Zero -> return Zero
  | End (f, e) ->
      let* e = e in
      let* f = sface_of_opt f in
      return (End (f, e))
  | Mid f ->
      let* f = sface_of_opt f in
      return (Mid f)

let rec opt_of_sface : type a b. (a, b) sface -> (a, b) opt_sface =
 fun f ->
  match f with
  | Zero -> Zero
  | End (f, e) -> End (opt_of_sface f, Some e)
  | Mid f -> Mid (opt_of_sface f)

let comp_opt_sface : type m n k. (n, k) opt_sface -> (m, n) opt_sface -> (m, k) opt_sface =
 fun x y -> Opt.comp_sface x y

let rec cod_sface : type m n. (m, n) sface -> n D.t = function
  | Zero -> Word Zero
  | End (f, _) ->
      let (Word s) = cod_sface f in
      Word (Suc (s, Unit))
  | Mid f ->
      let (Word s) = cod_sface f in
      Word (Suc (s, Unit))

(* Zero has only the trivial strict face *)
let sface_zero : type n. (n, D.zero) sface -> (n, D.zero) Eq.t = function
  | Zero -> Eq

type _ sface_of = SFace_of : ('m, 'n) sface -> 'n sface_of

(* Insert an element in the codomain and domain of a strict face, with the same numerical De Bruijn index. *)

type (_, _) insert_sface =
  | Insert_sface : ('m, 'msuc) D.insert * ('msuc, 'nsuc) sface -> ('m, 'nsuc) insert_sface

let rec insert_sface : type m n nsuc. (m, n) sface -> (n, nsuc) D.insert -> (m, nsuc) insert_sface =
 fun f i ->
  match i with
  | Now -> Insert_sface (Now, Mid f)
  | Later i -> (
      match f with
      | End (f, e) ->
          let (Insert_sface (i, f)) = insert_sface f i in
          Insert_sface (i, End (f, e))
      | Mid f ->
          let (Insert_sface (i, f)) = insert_sface f i in
          Insert_sface (Later i, Mid f))

(* Conversely, any strict face of a sum decomposes as a sum. *)

type (_, _, _) sface_of_plus =
  | SFace_of_plus :
      ('m, 'l, 'ml) D.plus * ('m, 'n) sface * ('l, 'k) sface
      -> ('ml, 'n, 'k) sface_of_plus

let rec sface_of_plus : type ml n k nk.
    (n, k, nk) D.plus -> (ml, nk) sface -> (ml, n, k) sface_of_plus =
 fun nk f ->
  match nk with
  | Zero -> SFace_of_plus (D.Zero, f, Zero)
  | Suc (nk, Unit) -> (
      match f with
      | End (f, e) ->
          let (SFace_of_plus (ml, f1, f2)) = sface_of_plus nk f in
          SFace_of_plus (ml, f1, End (f2, e))
      | Mid f ->
          let (SFace_of_plus (ml, f1, f2)) = sface_of_plus nk f in
          SFace_of_plus (Suc (ml, Unit), f1, Mid f2))

type (_, _) d_le = Le : ('m, 'n, 'mn) D.plus -> ('m, 'mn) d_le

let rec plus_of_sface : type m mn. (m, mn) sface -> (m, mn) d_le = function
  | Zero -> Le Zero
  | End (d, _) ->
      let (Le mn) = plus_of_sface d in
      Le (Suc (mn, Unit))
  | Mid d ->
      let (Le mn) = plus_of_sface d in
      Le (D.suc_plus_eq_suc mn)

(* As long as there is at least one endpoint, any dimension has at least one zero-dimensional face. *)

let rec vertex : type n. n D.t -> (D.zero, n) sface option = function
  | Word Zero -> Some Zero
  | Word (Suc (n, Unit)) -> (
      let open Monad.Ops (Monad.Maybe) in
      let (Wrap l) = Endpoints.wrapped () in
      match Endpoints.len l with
      | N.Nat (Suc _) ->
          let* s = vertex (Word n) in
          Some (End (s, (l, Top)))
      | N.Nat Zero -> None)

(* A strict face of a singleton dimension is either the identity or an endpoint. *)

let singleton_sface : type m n l.
    (m, n) sface -> n is_singleton -> l Endpoints.len -> [ `End of l N.index | `Mid of (m, n) Eq.t ]
    =
 fun s One l ->
  match s with
  | End (Zero, (l', i)) ->
      let Eq = Endpoints.uniq l l' in
      `End i
  | Mid Zero -> `Mid Eq

(* Converting to and from strings *)

type any_sface = Any_sface : ('n, 'k) sface -> any_sface

let rec string_of_sface : type n k. ?unicode:bool -> (n, k) sface -> string =
 fun ?(unicode = false) fa ->
  match fa with
  | Zero -> ""
  | End (fa, e) -> Endpoints.to_string ~unicode (Some e) ^ string_of_sface ~unicode fa
  | Mid fa -> Endpoints.to_string ~unicode None ^ string_of_sface ~unicode fa

let sface_of_string : string -> any_sface option =
 fun str ->
  let (Wrap l) = Endpoints.wrapped () in
  String.fold_right
    (fun x fa ->
      match (fa, Endpoints.of_char l x) with
      | None, _ | _, Error _ -> None
      | Some (Any_sface fa), Ok (Some e) -> Some (Any_sface (End (fa, e)))
      | Some (Any_sface fa), Ok None -> Some (Any_sface (Mid fa)))
    str (Some (Any_sface Zero))
