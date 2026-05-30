open Util

type (_, _, _, _) t = ..

module type Theory = sig
  type ('a, 'm, 'n, 'b) t

  val hsrc : ('a, 'm, 'n, 'b) t -> 'a Mode.t
  val htgt : ('a, 'm, 'n, 'b) t -> 'b Mode.t
  val vsrc : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) Modality.t
  val vtgt : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) Modality.t

  val compare :
    ('dom1, 'mu1, 'nu1, 'cod1) t ->
    ('dom2, 'mu2, 'nu2, 'cod2) t ->
    ('dom1 * 'mu1 * 'nu1 * 'cod1, 'dom2 * 'mu2 * 'nu2 * 'cod2) Eq.compare

  val id : ('dom, 'modality, 'cod) Modality.t -> ('dom, 'modality, 'modality, 'cod) t

  val hcomp :
    ('a, 'm, 'b, 'r, 'c, 'mr) Modality.comp ->
    ('a, 'n, 'b, 's, 'c, 'ns) Modality.comp ->
    ('b, 'r, 's, 'c) t ->
    ('a, 'm, 'n, 'b) t ->
    ('a, 'mr, 'ns, 'c) t

  val vcomp : ('a, 'n, 'r, 'b) t -> ('a, 'm, 'n, 'b) t -> ('a, 'm, 'r, 'b) t
  val find_unique : ('a, 'm, 'b) Modality.t -> ('a, 'n, 'b) Modality.t -> ('a, 'm, 'n, 'b) t option
  val to_string : ('a, 'm, 'n, 'b) t -> string
end

module type Internal_theory = Theory with type ('a, 'm, 'n, 'b) t := ('a, 'm, 'n, 'b) t

let theory : (module Internal_theory) ref =
  ref
    (module struct
      let hsrc _ = failwith "Modalcell.theory not set"
      let htgt _ = failwith "Modalcell.theory not set"
      let vsrc _ = failwith "Modalcell.theory not set"
      let vtgt _ = failwith "Modalcell.theory not set"
      let compare _ _ = failwith "Modalcell.theory not set"
      let id _ = failwith "Modalcell.theory not set"
      let hcomp _ _ _ _ = failwith "Modalcell.theory not set"
      let vcomp _ _ = failwith "Modalcell.theory not set"
      let find_unique _ _ = failwith "Modalcell.theory not set"
      let to_string _ = failwith "Modalcell.theory not set"
    end : Internal_theory)

let set_theory ((module T) : (module Theory)) =
  theory :=
    (module struct
      type ('a, 'm, 'n, 'b) t += U of ('a, 'm, 'n, 'b) T.t

      let hsrc = function
        | U a -> T.hsrc a
        | _ -> failwith "Modalcell: unknown constructor"

      let htgt = function
        | U a -> T.htgt a
        | _ -> failwith "Modalcell: unknown constructor"

      let vsrc = function
        | U a -> T.vsrc a
        | _ -> failwith "Modalcell: unknown constructor"

      let vtgt = function
        | U a -> T.vtgt a
        | _ -> failwith "Modalcell: unknown constructor"

      let compare a b =
        match (a, b) with
        | U a, U b -> T.compare a b
        | _ -> failwith "Modalcell: unknown constructor"

      let id m = U (T.id m)

      let hcomp mn rs a b =
        match (a, b) with
        | U a, U b -> U (T.hcomp mn rs a b)
        | _ -> failwith "Modalcell: unknown constructor"

      let vcomp a b =
        match (a, b) with
        | U a, U b -> U (T.vcomp a b)
        | _ -> failwith "Modalcell: unknown constructor"

      let find_unique m n =
        match T.find_unique m n with
        | Some a -> Some (U a)
        | None -> None

      let to_string = function
        | U a -> T.to_string a
        | _ -> failwith "Modalcell: unknown constructor"
    end : Internal_theory)

type (_, _) wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'b) wrapped
type (_, _, _) cod_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) cod_wrapped
type (_, _, _) dom_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) dom_wrapped
type _ cod2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'a cod2_wrapped
type _ dom2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'b dom2_wrapped

let hsrc : type a m n b. (a, m, n, b) t -> a Mode.t =
 fun x ->
  let module T = (val !theory) in
  T.hsrc x

let htgt : type a m n b. (a, m, n, b) t -> b Mode.t =
 fun x ->
  let module T = (val !theory) in
  T.htgt x

let vsrc : type a m n b. (a, m, n, b) t -> (a, m, b) Modality.t =
 fun x ->
  let module T = (val !theory) in
  T.vsrc x

let vtgt : type a m n b. (a, m, n, b) t -> (a, n, b) Modality.t =
 fun x ->
  let module T = (val !theory) in
  T.vtgt x

let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
    (dom1, mu1, nu1, cod1) t ->
    (dom2, mu2, nu2, cod2) t ->
    (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
 fun x y ->
  let module T = (val !theory) in
  T.compare x y

let id : type dom modality cod. (dom, modality, cod) Modality.t -> (dom, modality, modality, cod) t
    =
 fun m ->
  let module T = (val !theory) in
  T.id m

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
 fun mr ns x y ->
  let module T = (val !theory) in
  T.hcomp mr ns x y

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
 fun x y ->
  let module T = (val !theory) in
  T.vcomp x y

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
