open Util
open Singleton

(* ********** Strict faces ********** *)

(* A strict face is an order-preserving partial map that is surjective and with an endpoint index assigned to each element not mapping to the codomain. *)

type (_, _) sface =
  | Zero : (D.zero, D.zero) sface
  | End : ('m, 'n) sface * 'g D.G.t * 'l Endpoints.t -> ('m, ('n, 'g) D.suc) sface
  | Mid : ('m, 'n) sface * 'g D.G.t -> (('m, 'g) D.suc, ('n, 'g) D.suc) sface

let rec id_sface : type n. n D.t -> (n, n) sface = function
  | Word Zero -> Zero
  | Word (Suc (n, g)) -> Mid (id_sface (Word n), g)

let rec dom_sface : type m n. (m, n) sface -> m D.t = function
  | Zero -> Word Zero
  | End (f, _, _) ->
      let (Word s) = dom_sface f in
      Word s
  | Mid (f, g) ->
      let (Word s) = dom_sface f in
      Word (Suc (s, g))

let rec cod_sface : type m n. (m, n) sface -> n D.t = function
  | Zero -> Word Zero
  | End (f, g, _) ->
      let (Word s) = cod_sface f in
      Word (Suc (s, g))
  | Mid (f, g) ->
      let (Word s) = cod_sface f in
      Word (Suc (s, g))


let rec is_id_sface : type m n. (m, n) sface -> (m, n) Eq.t option = function
  | Zero -> Some Eq
  | End _ -> None
  | Mid (f, _) -> (
      match is_id_sface f with
      | Some Eq -> Some Eq
      | None -> None)

let rec comp_sface : type m n k. (n, k) sface -> (m, n) sface -> (m, k) sface =
 fun a b ->
  match (a, b) with
  | Zero, Zero -> Zero
  | End (a', g, e), _ -> End (comp_sface a' b, g, e)
  | Mid (a', _), End (b', g, e) -> End (comp_sface a' b', g, e)
  | Mid (a', g), Mid (b', _) -> Mid (comp_sface a' b', g)

(* Zero has only the trivial strict face *)
let sface_zero : type n. (n, D.zero) sface -> (n, D.zero) Eq.t = function
  | Zero -> Eq

type _ sface_of = SFace_of : ('m, 'n) sface -> 'n sface_of

(* Insert an element in the codomain and domain of a strict face, with the same numerical De Bruijn index. *)

type (_, _, _) insert_sface =
  | Insert_sface : ('m, 'g, 'msuc) D.insert * ('msuc, 'nsuc) sface -> ('m, 'g, 'nsuc) insert_sface

let rec insert_sface : type m n g nsuc.
    (m, n) sface -> g D.G.t -> (n, g, nsuc) D.insert -> (m, g, nsuc) insert_sface =
 fun f g i ->
  match i with
  | Now -> Insert_sface (Now, Mid (f, g))
  | Later i -> (
      match f with
      | End (f, h, e) ->
          let (Insert_sface (i, f)) = insert_sface f g i in
          Insert_sface (i, End (f, h, e))
      | Mid (f, h) ->
          let (Insert_sface (i, f)) = insert_sface f g i in
          Insert_sface (Later i, Mid (f, h)))

(* Concatenate two strict faces left-to-right. *)
let rec sface_plus_sface : type m n mn k p kp.
    (k, m) sface -> (m, n, mn) D.plus -> (k, p, kp) D.plus -> (p, n) sface -> (kp, mn) sface =
 fun fkm mn kp fpn ->
  match (fpn, mn, kp) with
  | Zero, Zero, Zero -> fkm
  | End (fpn, g, e), Suc (mn, _), kp -> End (sface_plus_sface fkm mn kp fpn, g, e)
  | Mid (fpn, g), Suc (mn, _), Suc (kp, _) -> Mid (sface_plus_sface fkm mn kp fpn, g)

(* In particular, we can extend by identities on the right or left. *)

let sface_plus : type m n mn k kn.
    (k, m) sface -> (m, n, mn) D.plus -> (k, n, kn) D.plus -> (kn, mn) sface =
 fun f mn kn -> sface_plus_sface f mn kn (id_sface (D.plus_right mn))

let plus_sface : type m n nm k nk.
    n D.t -> (n, m, nm) D.plus -> (n, k, nk) D.plus -> (k, m) sface -> (nk, nm) sface =
 fun n nm nk f -> sface_plus_sface (id_sface n) nm nk f

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
  | Suc (nk, _) -> (
      match f with
      | End (f, g, e) ->
          let (SFace_of_plus (ml, f1, f2)) = sface_of_plus nk f in
          SFace_of_plus (ml, f1, End (f2, g, e))
      | Mid (f, g) ->
          let (SFace_of_plus (ml, f1, f2)) = sface_of_plus nk f in
          SFace_of_plus (Suc (ml, g), f1, Mid (f2, g)))

type (_, _) d_le = Le : ('m, 'n, 'mn) D.plus -> ('m, 'mn) d_le

let plus_of_sface : type m mn. (m, mn) sface -> (m, mn) d_le =
 fun s ->
  match D.factor (cod_sface s) (dom_sface s) with
  | Some (Factor p) -> Le p
  | None -> assert false

(* As long as there is at least one endpoint, any dimension has at least one zero-dimensional face. *)

let rec vertex : type n. n D.t -> (D.zero, n) sface option = function
  | Word Zero -> Some Zero
  | Word (Suc (n, g)) -> (
      let open Monad.Ops (Monad.Maybe) in
      let (Wrap l) = Endpoints.wrapped () in
      match Endpoints.len l with
      | N.Nat (Suc _) ->
          let* s = vertex (Word n) in
          Some (End (s, g, (l, Top)))
      | N.Nat Zero -> None)

(* A strict face of a singleton dimension is either the identity or an endpoint. *)

let singleton_sface : type m n l.
    (m, n) sface -> n is_singleton -> l Endpoints.len -> [ `End of l N.index | `Mid of (m, n) Eq.t ]
    =
 fun s One l ->
  match s with
  | End (Zero, _, (l', i)) ->
      let Eq = Endpoints.uniq l l' in
      `End i
  | Mid (Zero, _) -> `Mid Eq

(* Converting to and from strings *)

type any_sface = Any_sface : ('n, 'k) sface -> any_sface

let rec string_of_sface : type n k. ?unicode:bool -> (n, k) sface -> string =
 fun ?(unicode = false) fa ->
  match fa with
  | Zero -> ""
  | End (fa, _, e) -> Endpoints.to_string ~unicode (Some e) ^ string_of_sface ~unicode fa
  | Mid (fa, _) -> Endpoints.to_string ~unicode None ^ string_of_sface ~unicode fa

let sface_of_string : string -> any_sface option =
 fun str ->
  let (Wrap l) = Endpoints.wrapped () in
  String.fold_right
    (fun x fa ->
      match (fa, Endpoints.of_char l x) with
      | None, _ | _, Error _ -> None
      | Some (Any_sface fa), Ok (Some e) -> Some (Any_sface (End (fa, D.deg, e)))
      | Some (Any_sface fa), Ok None -> Some (Any_sface (Mid (fa, D.deg))))
    str (Some (Any_sface Zero))
