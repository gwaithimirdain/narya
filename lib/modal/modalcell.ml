open Util
open Dim

type ('a, 'm, 'n, 'b) gen =
  | PK : ('a, 'm, 'b) Modality.t * int * ('a, 'n, 'b) Modality.t -> ('a, 'm, 'n, 'b) gen

let count = ref 0

module Gen = struct
  type ('a, 'm, 'n, 'b) t = ('a, 'm, 'n, 'b) gen

  let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
      (dom1, mu1, nu1, cod1) t ->
      (dom2, mu2, nu2, cod2) t ->
      (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
   fun (PK (m, x, n)) (PK (r, y, s)) ->
    match (Modality.compare m r, Modality.compare n s, x = y) with
    | Eq, Eq, true -> Eq
    | _ -> Neq
end

let generate : type a m n b. (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) gen =
 fun m n ->
  let x = !count in
  count := !count + 1;
  PK (m, x, n)

type (_, _, _, _) t =
  | Gen : ('a, 'm, 'n, 'b) gen -> ('a, 'm, 'n, 'b) t
  | Id : ('a, 'm, 'b) Modality.t -> ('a, 'm, 'm, 'b) t
  | Hcomp :
      ('a, 'm, 'b, 'r, 'c, 'mr) Modality.comp
      * ('a, 'n, 'b, 's, 'c, 'ns) Modality.comp
      * ('b, 'r, 's, 'c) t
      * ('a, 'm, 'n, 'b) t
      -> ('a, 'mr, 'ns, 'c) t
  | Vcomp : ('a, 'n, 'r, 'b) t * ('a, 'm, 'n, 'b) t -> ('a, 'm, 'r, 'b) t

let of_gen : type a m n b. (a, m, n, b) gen -> (a, m, n, b) t = fun x -> Gen x

module type Theory = sig
  val compare : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'n, 'b) t -> bool
  val find_unique : ('a, 'm, 'b) Modality.t -> ('a, 'n, 'b) Modality.t -> ('a, 'm, 'n, 'b) t option
  val to_string : ('a, 'm, 'n, 'b) t -> string

  val filter_deg :
    ('a, 'm, 'n, 'b) t ->
    'z D.t ->
    ('a, 'm, 'b, 'x, 'z) Modality.filter_dim ->
    ('a, 'n, 'b, 'y, 'z) Modality.filter_dim ->
    ('y, 'x) deg
end

let theory : (module Theory) ref =
  ref
    (module struct
      let compare _ _ = failwith "Modalcell.theory not set"
      let find_unique _ _ = failwith "Modalcell.theory not set"
      let to_string _ = failwith "Modalcell.theory not set"
      let filter_deg _ _ _ = failwith "Modalcell.theory not set"
    end : Theory)

let choose_theory (t : (module Theory)) = theory := t

type (_, _) wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'b) wrapped
type (_, _, _) cod_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) cod_wrapped
type (_, _, _) dom_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) dom_wrapped
type _ cod2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'a cod2_wrapped
type _ dom2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'b dom2_wrapped

let rec hsrc : type a m n b. (a, m, n, b) t -> a Mode.t = function
  | Gen (PK (m, _, _)) -> Modality.src m
  | Id m -> Modality.src m
  | Hcomp (_, _, _, x) -> hsrc x
  | Vcomp (_, x) -> hsrc x

let rec htgt : type a m n b. (a, m, n, b) t -> b Mode.t = function
  | Gen (PK (m, _, _)) -> Modality.tgt m
  | Id m -> Modality.tgt m
  | Hcomp (_, _, y, _) -> htgt y
  | Vcomp (_, x) -> htgt x

let rec vsrc : type a m n b. (a, m, n, b) t -> (a, m, b) Modality.t = function
  | Gen (PK (m, _, _)) -> m
  | Id m -> m
  | Hcomp (mr, _, y, _) -> Modality.comp_out (vsrc y) mr
  | Vcomp (_, x) -> vsrc x

let rec vtgt : type a m n b. (a, m, n, b) t -> (a, n, b) Modality.t = function
  | Gen (PK (_, _, n)) -> n
  | Id m -> m
  | Hcomp (_, ns, y, _) -> Modality.comp_out (vtgt y) ns
  | Vcomp (y, _) -> vtgt y

let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
    (dom1, mu1, nu1, cod1) t ->
    (dom2, mu2, nu2, cod2) t ->
    (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
 fun x y ->
  let module T = (val !theory) in
  match (Modality.compare (vsrc x) (vsrc y), Modality.compare (vtgt x) (vtgt y)) with
  | Eq, Eq -> if T.compare x y then Eq else Neq
  | _ -> Neq

let id : type dom modality cod. (dom, modality, cod) Modality.t -> (dom, modality, modality, cod) t
    =
 fun m -> Id m

let id2 : type mode. mode Mode.t -> (mode, mode Modality.id, mode Modality.id, mode) t =
 fun x -> id (Modality.id x)

let compare_id : type dom mu nu cod.
    (dom, mu, nu, cod) t -> (dom * mu * nu, cod * dom Modality.id * dom Modality.id) Eq.compare =
 fun x ->
  match compare x (id2 (hsrc x)) with
  | Eq -> Eq
  | Neq -> Neq

let hcomp : type a m n b r s c mr ns.
    (a, m, b, r, c, mr) Modality.comp ->
    (a, n, b, s, c, ns) Modality.comp ->
    (b, r, s, c) t ->
    (a, m, n, b) t ->
    (a, mr, ns, c) t =
 fun mr ns x y -> Hcomp (mr, ns, x, y)

let hcomp_wrapped : type a m n b r s c. (b, m, n, c) t -> (a, r, s, b) t -> (a, c) wrapped =
 fun x y ->
  let (Comp mr) = Modality.comp (vsrc y) in
  let (Comp ns) = Modality.comp (vtgt y) in
  Wrap (hcomp mr ns x y)

let postwhisker : type a r s b m c mr ms.
    (a, r, b, m, c, mr) Modality.comp ->
    (a, s, b, m, c, ms) Modality.comp ->
    (b, m, c) Modality.t ->
    (a, r, s, b) t ->
    (a, mr, ms, c) t =
 fun mr ms m x -> hcomp mr ms (id m) x

let postwhisker_wrapped : type a r s b m c. (b, m, c) Modality.t -> (a, r, s, b) t -> (a, c) wrapped
    =
 fun m x -> hcomp_wrapped (id m) x

let prewhisker : type a r b m n c mr nr.
    (a, r, b, m, c, mr) Modality.comp ->
    (a, r, b, n, c, nr) Modality.comp ->
    (b, m, n, c) t ->
    (a, r, b) Modality.t ->
    (a, mr, nr, c) t =
 fun mr nr x m -> hcomp mr nr x (id m)

let prewhisker_wrapped : type a r b m n c. (b, m, n, c) t -> (a, r, b) Modality.t -> (a, c) wrapped
    =
 fun x m -> hcomp_wrapped x (id m)

let vcomp : type a m n r b. (a, n, r, b) t -> (a, m, n, b) t -> (a, m, r, b) t =
 fun x y -> Vcomp (x, y)

let vcomp_extending : type a m k kn b n s c.
    (c, k, b) Modality.t ->
    (a, n, c, k, b, kn) Modality.comp ->
    (a, n, s, c) t ->
    (a, m, kn, b) t ->
    (a, m, b) cod_wrapped =
 fun k compn x y ->
  let (Comp comps) = Modality.comp (vtgt x) in
  let kx = postwhisker compn comps k x in
  Wrap (vcomp kx y)

type (_, _, _, _, _, _) find_unique =
  | Unique : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b, 'a, 'n, 'b) find_unique

let find_unique : type a m n b c d.
    (a, m, b) Modality.t -> (c, n, d) Modality.t -> (a, m, b, c, n, d) find_unique option =
 fun m n ->
  let module T = (val !theory) in
  match
    (Mode.compare (Modality.src m) (Modality.src n), Mode.compare (Modality.tgt m) (Modality.tgt n))
  with
  | Eq, Eq -> (
      match T.find_unique m n with
      | Some a -> Some (Unique a)
      | None -> None)
  | _ -> None

let to_string : type a m n b. (a, m, n, b) t -> string =
 fun m ->
  let module T = (val !theory) in
  T.to_string m

let filter_deg : type a m n b x y z.
    (a, m, n, b) t ->
    z D.t ->
    (a, m, b, x, z) Modality.filter_dim ->
    (a, n, b, y, z) Modality.filter_dim ->
    (y, x) deg =
 fun a z fm fn ->
  let module T = (val !theory) in
  T.filter_deg a z fm fn
