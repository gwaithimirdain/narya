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

type (_, _, _, _) adjunction =
  | Adjunction : {
      left : ('a, 'f, 'b) Modality.t;
      right : ('b, 'g, 'a) Modality.t;
      right_left : ('a, 'f, 'b, 'g, 'a, 'gf) Modality.comp;
      unit : ('a, 'a Modality.id, 'gf, 'a) t;
      left_right : ('b, 'g, 'a, 'f, 'b, 'fg) Modality.comp;
      counit : ('b, 'fg, 'b Modality.id, 'b) t;
    }
      -> ('a, 'f, 'g, 'b) adjunction

type (_, _, _) sinister = Sinister : ('a, 'f, 'g, 'b) adjunction -> ('a, 'f, 'b) sinister

(* An adjunction with a specified source mode but everything else existential. *)
type _ any_adjunction = Any_adjunction : ('a, 'f, 'g, 'b) adjunction -> 'a any_adjunction

let id_adjunction : type a. a Mode.t -> (a, a Modality.id, a Modality.id, a) adjunction =
 fun a ->
  let id = Modality.id a in
  Adjunction
    {
      left = id;
      right = id;
      right_left = Modality.comp_id id;
      left_right = Modality.comp_id id;
      unit = Id id;
      counit = Id id;
    }

let id_sinister : type a. a Mode.t -> (a, a Modality.id, a) sinister =
 fun a -> Sinister (id_adjunction a)

(* Accessors for the data of an adjunction. *)
let adj_left : type a f g b. (a, f, g, b) adjunction -> (a, f, b) Modality.t = function
  | Adjunction { left; _ } -> left

let adj_right : type a f g b. (a, f, g, b) adjunction -> (b, g, a) Modality.t = function
  | Adjunction { right; _ } -> right

(* Decide whether an adjunction is the identity adjunction, giving type-level equations if so.  This is used to take fast paths (and preserve pre-modal behavior exactly) for ordinary non-modal fields, which are stored as fields modal over the identity adjunction. *)
let compare_adjunction_id : type a f g b.
    (a, f, g, b) adjunction -> (f * g * b, a Modality.id * a Modality.id * a) Eq.compare = function
  | Adjunction { left; right; _ } -> (
      match Modality.compare_id left with
      | Neq -> Neq
      | Eq -> (
          match Modality.compare_id right with
          | Neq -> Neq
          | Eq -> Eq))

type _ parametric_locker =
  | Locker : ('a, 'm, 'a) Modality.t * ('a, 'm, 'a Modality.id, 'a) t -> 'a parametric_locker

module type Theory = sig
  val sinister : ('a, 'm, 'b) Modality.t -> ('a, 'm, 'b) sinister option
  val compare : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'n, 'b) t -> bool
  val find_unique : ('a, 'm, 'b) Modality.t -> ('a, 'n, 'b) Modality.t -> ('a, 'm, 'n, 'b) t option
  val parametric_locker : 'a Mode.t -> ('a parametric_locker, string) Result.t
  val to_string : ('a, 'm, 'n, 'b) t -> string
end

let theory : (module Theory) ref =
  ref
    (module struct
      let sinister _ = failwith "Modalcell.theory not set"
      let compare _ _ = failwith "Modalcell.theory not set"
      let find_unique _ _ = failwith "Modalcell.theory not set"
      let parametric_locker _ = Error "undefined mode theory"
      let to_string _ = failwith "Modalcell.theory not set"
    end : Theory)

let choose_theory (t : (module Theory)) = theory := t

(* Ask the current theory whether a modality is sinister (a declared left adjoint), obtaining the adjunction data if so. *)
let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) sinister option =
 fun f ->
  let module T = (val !theory) in
  T.sinister f

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

let rec bprewhisker : type a r b m n c mr nr.
    (a, r, b, m, c, mr) Modality.bcomp ->
    (a, r, b, n, c, nr) Modality.bcomp ->
    (b, m, n, c) t ->
    (a, mr, nr, c) t =
 fun mr nr x ->
  match (mr, nr) with
  | Zero, Zero -> x
  | Suc (g1, mr), Suc (g2, nr) ->
      let Eq = Modality.Gen.src_uniq g1 g2 in
      bprewhisker mr nr
        (prewhisker
           (Suc (Zero, g1))
           (Suc (Zero, g2))
           x
           (Path (Suc (Zero, g2), Modality.Gen.tgt g2)))

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

let parametric_locker m =
  let module T = (val !theory) in
  if Endpoints.internal () then Locker (Modality.id m, id2 m)
  else
    match T.parametric_locker m with
    | Ok l -> l
    | Error str -> failwith ("mode theory " ^ str ^ " doesn't support external parametricity")

let to_string : type a m n b. (a, m, n, b) t -> string =
 fun m ->
  let module T = (val !theory) in
  T.to_string m
