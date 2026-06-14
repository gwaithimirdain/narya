open Bwd
open Util
open Dim
open Signatures
module StringMap = Map.Make (String)

type ('a, 'm, 'b) gen = PK : 'a Mode.t * int * 'b Mode.t -> ('a, unit, 'b) gen

module Gen = struct
  module Obj = Mode

  type ('src, 'morphism, 'tgt) t = ('src, 'morphism, 'tgt) gen
  type all_wrapped = Wrap : ('src, 'morphism, 'tgt) gen -> all_wrapped

  let src : type src gen tgt. (src, gen, tgt) t -> src Obj.t = fun (PK (a, _, _)) -> a
  let tgt : type src gen tgt. (src, gen, tgt) t -> tgt Obj.t = fun (PK (_, _, b)) -> b
  let names : string Dynarray.t = Dynarray.create ()

  let compare : type a1 m1 b1 a2 m2 b2.
      (a1, m1, b1) t -> (a2, m2, b2) t -> (a1 * m1 * b1, a2 * m2 * b2) Eq.compare =
   fun (PK (a1, i, b1)) (PK (a2, j, b2)) ->
    match (Mode.compare a1 a2, Mode.compare b1 b2, i = j) with
    | Eq, Eq, true -> Eq
    | _ -> Neq

  let name : type src gen tgt. (src, gen, tgt) t -> string =
   fun (PK (_, i, _)) -> Dynarray.get names i

  let nonparametric : D.wrapped Dynarray.t = Dynarray.create ()

  let src_uniq : type a1 m b1 a2 b2. (a1, m, b1) t -> (a2, m, b2) t -> (a1, a2) Eq.t =
   fun m n ->
    match compare m n with
    | Eq -> Eq
    | Neq -> failwith "src_uniq"

  let tgt_uniq : type a1 m b1 a2 b2. (a1, m, b1) t -> (a2, m, b2) t -> (b1, b2) Eq.t =
   fun m n ->
    match compare m n with
    | Eq -> Eq
    | Neq -> failwith "src_uniq"

  let by_name : all_wrapped StringMap.t ref = ref StringMap.empty

  module Gen = struct
    type nonrec ('a, 'm, 'b) t = ('a, 'm, 'b) t
  end

  module Map = struct
    module Key = Gen

    module Make (F : Fam4) = struct
      module Key = Key
      module F = F
      module IntMap = Map.Make (Int)

      module Tgt = struct
        type (_, _) t = Wrap : ('b, 'src, unit, 'tgt) F.t IntMap.t -> ('b * 'src, 'tgt) t
      end

      module TgtMap = Mode.Map.Make (Tgt)

      module Src = struct
        type ('b, 'src) t = ('b * 'src) TgtMap.t
      end

      module SrcMap = Mode.Map.Make (Src)

      type 'a t = 'a SrcMap.t

      let empty : type b. b t = SrcMap.empty

      open Monad.Ops (Monad.Maybe)

      let find_opt : type src g tgt b. (src, g, tgt) Key.t -> b t -> (b, src, g, tgt) F.t option =
       fun (PK (a, i, b)) m ->
        let* srcmap = SrcMap.find_opt a m in
        let* (Wrap tgtmap) = TgtMap.find_opt b srcmap in
        IntMap.find_opt i tgtmap

      let add : type src g tgt b. (src, g, tgt) Key.t -> (b, src, g, tgt) F.t -> b t -> b t =
       fun (PK (a, i, b)) x m ->
        SrcMap.update a
          (fun y ->
            Some
              (TgtMap.update b
                 (fun z ->
                   Some
                     (Wrap
                        (IntMap.add i x
                           (match z with
                           | Some (Wrap m) -> m
                           | None -> IntMap.empty))))
                 (Option.value y ~default:TgtMap.empty)))
          m

      let update : type src g tgt b.
          (src, g, tgt) Key.t ->
          ((b, src, g, tgt) F.t option -> (b, src, g, tgt) F.t option) ->
          b t ->
          b t =
       fun (PK (a, i, b)) f m ->
        SrcMap.update a
          (fun y ->
            Some
              (TgtMap.update b
                 (fun z ->
                   Some
                     (Wrap
                        (IntMap.update i f
                           (match z with
                           | Some (Wrap m) -> m
                           | None -> IntMap.empty))))
                 (Option.value y ~default:TgtMap.empty)))
          m

      let remove : type src g tgt b. (src, g, tgt) Key.t -> b t -> b t =
       fun (PK (a, i, b)) m ->
        SrcMap.update a
          (function
            | Some y ->
                Some
                  (TgtMap.update b
                     (function
                       | Some (Wrap z) -> Some (Wrap (IntMap.remove i z))
                       | None -> None)
                     y)
            | None -> None)
          m

      type 'a mapper = {
        map :
          'src 'g 'tgt.
          ('src, 'g, 'tgt) Key.t -> ('a, 'src, 'g, 'tgt) F.t -> ('a, 'src, 'g, 'tgt) F.t;
      }

      let map : type a. a mapper -> a t -> a t =
       fun mapper m ->
        SrcMap.map
          {
            map =
              (fun a y ->
                TgtMap.map
                  {
                    map =
                      (fun b -> function
                        | Wrap z -> Wrap (IntMap.mapi (fun i x -> mapper.map (PK (a, i, b)) x) z));
                  }
                  y);
          }
          m

      type 'a iterator = {
        it : 'src 'g 'tgt. ('src, 'g, 'tgt) Key.t -> ('a, 'src, 'g, 'tgt) F.t -> unit;
      }

      let iter : type a. a iterator -> a t -> unit =
       fun iterator m ->
        SrcMap.iter
          {
            it =
              (fun a y ->
                TgtMap.iter
                  {
                    it =
                      (fun b -> function
                        | Wrap z -> IntMap.iter (fun i x -> iterator.it (PK (a, i, b)) x) z);
                  }
                  y);
          }
          m
    end
  end

  module MapCheck : MAP3_MAKER with module Key = Gen = Map
end

module type Generator = sig
  type src
  type tgt

  val src : src Mode.t
  val tgt : tgt Mode.t
  val name : string

  (* Which directions this generator forbids parametricity in *)
  type nonparametric

  val nonparametric : nonparametric D.t
end

module type Generated = sig
  module G : Generator

  type t

  val modality : (G.src, t, G.tgt) gen
end

module Generate (G : Generator) = struct
  type t = unit

  let modality : (G.src, t, G.tgt) gen = PK (G.src, Dynarray.length Gen.names, G.tgt)

  let () =
    Dynarray.add_last Gen.names G.name;
    Dynarray.add_last Gen.nonparametric (Wrap G.nonparametric);
    Gen.by_name := StringMap.add G.name (Wrap modality : Gen.all_wrapped) !Gen.by_name
end

type ('src, 'tgt) gen_wrapped = Wrap : ('src, 'morphism, 'tgt) Gen.t -> ('src, 'tgt) gen_wrapped

let generate : type a b p. a Mode.t -> b Mode.t -> string -> p D.t -> (a, b) gen_wrapped =
 fun a b c p ->
  let module G = struct
    type src = a
    type tgt = b

    let src = a
    let tgt = b
    let name = c

    type nonparametric = p

    let nonparametric = p
  end in
  let module M = Generate (G) in
  Wrap M.modality

module Modality = Path.Make (Gen)
include Modality
module Map = Path.Map (Gen) (Mode.Map) (Gen.Map)

let locker : type a. a Mode.t -> (a, a) wrapped = fun _ -> raise (Failure "Modality.locker not set")

module Cube (F : Fam3) = struct
  module Parent = struct
    type ('a, 'm, 'b) modality_t = ('a, 'm, 'b) t
  end

  open Parent

  type (_, _, _, _) t =
    | Modal :
        ('dom, 'modality, 'mode) modality_t * ('n, ('dom, 'a, 'b) F.t) Dim.CubeOf.t
        -> ('n, 'mode, 'a, 'b) t
end

let compare_id : type x m y. (x, m, y) t -> (m * y, x id * x) Eq.compare =
 fun m ->
  match compare m (id (src m)) with
  | Eq -> Eq
  | Neq -> Neq

(* String names.  A modality is named by a string list of generator names.  Note that the empty list therefore represents the identity modality at *any* mode, so to convert such a name to a modality we need either the source or the target mode given. *)

let rec name_bwd : type a m b. (a, m, b) t -> string Bwd.t = function
  | Path (Zero, _) -> Emp
  | Path (Suc (Zero, g), _) -> Snoc (Emp, Gen.name g)
  | Path (Suc ((Suc (_, _) as gs), g), mode) -> Snoc (name_bwd (Path (gs, mode)), Gen.name g)

let name : type a m b. (a, m, b) t -> string list = fun m -> Bwd.to_list (name_bwd m)

let of_name_tgt : type a s.
    (s -> string) ->
    a Mode.t ->
    s list ->
    (a src_wrapped, [ `Not_found of s | `Wrong_tgt of Mode.wrapped * s * Mode.wrapped ]) result =
 fun get_string mode cs ->
  let rec go (m : a src_wrapped) = function
    | [] -> Ok m
    | c :: cs -> (
        match StringMap.find_opt (get_string c) !Gen.by_name with
        | None -> Error (`Not_found c)
        | Some (Wrap n) -> (
            let (Wrap m) = m in
            match Mode.compare (Gen.tgt n) (src m) with
            | Eq -> go (Wrap (suc m n)) cs
            | Neq -> Error (`Wrong_tgt (Mode.Wrap (Gen.tgt n), c, Mode.Wrap (src m))))) in
  go (Wrap (id mode)) cs

let rec of_name_src_bwd : type a s.
    (s -> string) ->
    s Bwd.t ->
    a Mode.t ->
    (a tgt_wrapped, [ `Not_found of s | `Wrong_src of Mode.wrapped * s * Mode.wrapped ]) result =
 fun get_string cs mode ->
  match cs with
  | Emp -> Ok (Wrap (id mode))
  | Snoc (cs, c) -> (
      match StringMap.find_opt (get_string c) !Gen.by_name with
      | None -> Error (`Not_found c)
      | Some (Wrap n) -> (
          match Mode.compare (Gen.src n) mode with
          | Eq -> (
              match of_name_src_bwd get_string cs (Gen.tgt n) with
              | Ok (Wrap m) -> Ok (Wrap (suc m n) : a tgt_wrapped)
              | Error e -> Error e)
          | Neq -> Error (`Wrong_src (Wrap (Gen.src n), c, Wrap mode))))

let of_name_src : type a s.
    (s -> string) ->
    s list ->
    a Mode.t ->
    (a tgt_wrapped, [ `Not_found of s | `Wrong_src of Mode.wrapped * s * Mode.wrapped ]) result =
 fun get_string cs mode -> of_name_src_bwd get_string (Bwd.of_list cs) mode

let to_string : type a m b. (a, m, b) t -> string =
 fun m ->
  match name m with
  | [] -> "id"
  | ms -> String.concat " " ms

let compare_name : type x m y s.
    (s -> string) ->
    s list ->
    (x, m, y) t ->
    ( unit,
      [ `Unequal of y src_wrapped | `Not_found of s | `Wrong_tgt of Mode.wrapped * s * Mode.wrapped ]
    )
    result =
 fun get_string name m ->
  match of_name_tgt get_string (tgt m) name with
  | Error e -> Error (e :> [ `Unequal of y src_wrapped | `Not_found of s | `Wrong_tgt of _ ])
  | Ok (Wrap n) -> (
      match compare m n with
      | Eq -> Ok ()
      | Neq -> Error (`Unequal (Wrap n)))

(* Nonparametric modalities *)

(* A modality is nonparametric for a direction if *any* of the generators in it are.  That is, nonparametric modalities are both a sieve and a cosieve.  Since we represent nonparametricity by a word of directions, i.e. a dimension, this means nonparametricity is a functor from the category of modalities to the one-object category of dimensions, determined by its action on generators. *)

module BD = Category.OneObject (D)

module Nonparam_gen = struct
  module Dom = Gen
  module Cod = BD

  module Obj = struct
    module Dom = Mode
    module Cod = Unitcomparable

    type (_, _) t = To_unit : 'a Mode.t -> ('a, unit) t

    let dom : type a u. (a, u) t -> a Mode.t = fun (To_unit x) -> x
    let cod : type a u. (a, u) t -> u Unitcomparable.t = fun (To_unit _) -> Unit

    type _ exists = Exists : ('a, 'x) t -> 'a exists

    let exists x = Exists (To_unit x)

    let uniq : type a x1 x2. (a, x1) t -> (a, x2) t -> (x1, x2) Eq.t =
     fun (To_unit _) (To_unit _) -> Eq
  end

  type (_, _, _, _, _, _) t =
    | Nonparametric : ('x, 'm, 'y) Gen.t * 'e D.t -> ('x, 'm, 'y, unit, 'e, unit) t

  let dom : type x m y u e v. (x, m, y, u, e, v) t -> (x, m, y) Gen.t =
   fun (Nonparametric (m, _)) -> m

  let cod : type x m y u e v. (x, m, y, u, e, v) t -> (u, e, v) BD.t =
   fun (Nonparametric (_, e)) -> BD.Loop e

  let src : type x m y u e v. (x, m, y, u, e, v) t -> (x, u) Obj.t =
   fun (Nonparametric (m, _)) -> Obj.To_unit (Gen.src m)

  let tgt : type x m y u e v. (x, m, y, u, e, v) t -> (y, v) Obj.t =
   fun (Nonparametric (m, _)) -> Obj.To_unit (Gen.tgt m)

  type (_, _, _) exists = Exists : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) exists

  let exists : type x m y. (x, m, y) Gen.t -> (x, m, y) exists =
   fun (PK (_, g, _) as m) ->
    let (Wrap e) = Dynarray.get Gen.nonparametric g in
    Exists (Nonparametric (m, e))

  let uniq : type x m y u1 e1 v1 u2 e2 v2.
      (x, m, y, u1, e1, v1) t -> (x, m, y, u2, e2, v2) t -> (u1 * e1 * v1, u2 * e2 * v2) Eq.t =
   fun (Nonparametric (_, e1)) (Nonparametric (_, e2)) ->
    match D.compare e1 e2 with
    | Eq -> Eq
    | Neq -> failwith "modality claimed to have two different nonparametricities"
end

module Nonparametric = Path.Hom (Gen) (BD) (Nonparam_gen)

type (_, _, _, _, _) filter_dim =
  | Filter :
      ('x, 'm, 'y, unit, 'e, unit) Nonparametric.t * ('e, 'a, 'b) except
      -> ('x, 'm, 'y, 'a, 'b) filter_dim

type (_, _, _, _) has_filter =
  | Has_filter : ('x, 'm, 'y, 'a, 'b) filter_dim -> ('x, 'm, 'y, 'b) has_filter

let filter : type x m y b. (x, m, y) t -> b D.t -> (x, m, y, b) has_filter =
 fun m b ->
  let (Exists e) = Nonparametric.exists m in
  let (Loop d) = Nonparametric.cod e in
  let (Except ex) = except_dirs d b in
  Has_filter (Filter (e, ex))

let filter_uniq : type x m y b a1 a2.
    (x, m, y, a1, b) filter_dim -> (x, m, y, a2, b) filter_dim -> (a1, a2) Eq.t =
 fun (Filter (m1, e1)) (Filter (m2, e2)) ->
  let Eq = Nonparametric.uniq m1 m2 in
  let Eq = except_uniq e1 e2 in
  Eq

(* A filter_dim is by a particular modality, which determines its source and target modes; so two filter_dims by the same modality (or a filter_dim and a modality) have the same source and target.  This is needed to recover modes that have been bound existentially elsewhere (e.g. in Plusmap.uninsert) before they can be compared with filter_uniq. *)
let filter_dim_modes : type x m y a b x2 y2.
    (x, m, y, a, b) filter_dim -> (x2, m, y2) t -> (x, x2) Eq.t * (y, y2) Eq.t =
 fun (Filter (n, _)) mu ->
  let d = Nonparametric.dom n in
  (src_uniq d mu, tgt_uniq d mu)

let filtered b (Filter (_, e)) = excepted e b

let filter_id : type mode a. mode Mode.t -> a D.t -> (mode, mode id, mode, a, a) filter_dim =
 fun mode a -> Filter (Nonparametric.id (To_unit mode), except_nothing a)

let eq_of_filter_id : type mode a b. (mode, mode id, mode, a, b) filter_dim -> (a, b) Eq.t =
 fun (Filter (p, ex)) ->
  let (Loop p) = Nonparametric.cod p in
  match D.compare_zero p with
  | Zero -> eq_of_except_nothing ex
  | Pos _ -> failwith "eq_of_filter_id"

let filter_idempotent : type x m y a b. (x, m, y, a, b) filter_dim -> (x, m, y, a, a) filter_dim =
 fun (Filter (e, ex)) -> Filter (e, except_idempotent ex)

let filter_zero : type x m y. (x, m, y) t -> (x, m, y, D.zero, D.zero) filter_dim =
 fun m ->
  let (Exists e) = Nonparametric.exists m in
  let (Loop _) = Nonparametric.cod e in
  Filter (e, except_zero)

let filter_plus : type x m y a b c d ac bd.
    (a, c, ac) D.plus ->
    (b, d, bd) D.plus ->
    (x, m, y, a, b) filter_dim ->
    (x, m, y, c, d) filter_dim ->
    (x, m, y, ac, bd) filter_dim =
 fun ac bd (Filter (e1, eab)) (Filter (e2, ecd)) ->
  let Eq = Nonparametric.uniq e1 e2 in
  Filter (e1, except_plus ac bd eab ecd)

type (_, _, _, _, _, _) filter_of_plus =
  | Filter_of_plus :
      ('a, 'c, 'ac) D.plus * ('x, 'm, 'y, 'a, 'b) filter_dim * ('x, 'm, 'y, 'c, 'd) filter_dim
      -> ('x, 'm, 'y, 'b, 'd, 'ac) filter_of_plus

let filter_of_plus : type x m y b d ac bd.
    (b, d, bd) D.plus -> (x, m, y, ac, bd) filter_dim -> (x, m, y, b, d, ac) filter_of_plus =
 fun bd (Filter (e, eacbd)) ->
  let (Except_of_plus (ac, eab, ecd)) = except_of_plus bd eacbd in
  Filter_of_plus (ac, Filter (e, eab), Filter (e, ecd))

type (_, _, _, _, _, _) filter_of_plus' =
  | Filter_of_plus' :
      ('b, 'c, 'bc) D.plus * ('bc, 'd) perm * ('x, 'm, 'y, 'a, 'b) filter_dim
      -> ('x, 'm, 'y, 'a, 'c, 'd) filter_of_plus'

let filter_of_plus' : type a c ac x m y d.
    d D.t -> (a, c, ac) D.plus -> (x, m, y, ac, d) filter_dim -> (x, m, y, a, c, d) filter_of_plus'
    =
 fun d ac (Filter (e, eacd)) ->
  let (Except_of_plus' (bc, p, eab)) = except_of_plus' d ac eacd in
  Filter_of_plus' (bc, p, Filter (e, eab))

type (_, _, _, _, _) filter_sface =
  | Filter_sface :
      ('d, 'a) sface * ('x, 'm, 'y, 'd, 'c) filter_dim
      -> ('x, 'm, 'y, 'a, 'c) filter_sface

let filter_sface : type x m y a b c.
    (x, m, y, a, b) filter_dim -> (c, b) sface -> (x, m, y, a, c) filter_sface =
 fun (Filter (e, ex)) s ->
  let (Except_sface (s, ex)) = except_sface ex s in
  Filter_sface (s, Filter (e, ex))

type (_, _, _, _, _) filter_deg =
  | Filter_deg : ('d, 'a) deg * ('x, 'm, 'y, 'd, 'c) filter_dim -> ('x, 'm, 'y, 'a, 'c) filter_deg

let filter_deg : type x m y a b c.
    (x, m, y, a, b) filter_dim -> (c, b) deg -> (x, m, y, a, c) filter_deg =
 fun (Filter (e, ex)) s ->
  let (Loop p) = Nonparametric.cod e in
  let (Except_deg (s, ex)) = except_deg p ex s in
  Filter_deg (s, Filter (e, ex))

type (_, _, _, _, _) filter_op =
  | Filter_op : ('d, 'a) op * ('x, 'm, 'y, 'd, 'c) filter_dim -> ('x, 'm, 'y, 'a, 'c) filter_op

let filter_op : type x m y a b c.
    (x, m, y, a, b) filter_dim -> (c, b) op -> (x, m, y, a, c) filter_op =
 fun filt (Op (fa, s)) ->
  let (Filter_sface (fa, filt)) = filter_sface filt fa in
  let (Filter_deg (s, filt)) = filter_deg filt s in
  Filter_op (Op (fa, s), filt)

type (_, _, _, _, _) filter_perm =
  | Filter_perm :
      ('d, 'a) perm * ('x, 'm, 'y, 'd, 'c) filter_dim
      -> ('x, 'm, 'y, 'a, 'c) filter_perm

let filter_perm : type x m y a b c.
    (x, m, y, a, b) filter_dim -> (c, b) perm -> (x, m, y, a, c) filter_perm =
 fun (Filter (e, ex)) s ->
  let (Loop p) = Nonparametric.cod e in
  let (Except_perm (s, ex)) = except_perm p ex s in
  Filter_perm (s, Filter (e, ex))

let deg_of_filter : type x m y a b. b D.t -> (x, m, y, a, b) filter_dim -> (b, a) deg =
 fun b (Filter (_, ex)) -> deg_of_except b ex

(* The strict face including the filtered sub-cube, a section of deg_of_filter.  It fixes an arbitrarily chosen endpoint in each filtered-away direction, which is semantically justified because the data in those directions is inaccessible behind a nonparametric lock. *)
let sface_of_filter : type x m y a b. b D.t -> (x, m, y, a, b) filter_dim -> (a, b) sface =
 fun b (Filter (_, ex)) ->
  let (Wrap l) = Endpoints.wrapped () in
  match Endpoints.indices l with
  | Snoc (_, e) -> sface_of_except e b ex
  | Emp -> failwith "sface_of_filter with no endpoints"

let filter_comp : type x y z m n nm a b c.
    (x, m, y, n, z, nm) comp ->
    (y, n, z, b, c) filter_dim ->
    (x, m, y, a, b) filter_dim ->
    (x, nm, z, a, c) filter_dim =
 fun n_m (Filter (f_n, ex_n)) (Filter (f_m, ex_m)) ->
  let (Comp (f_nm, Loopcomp n_m)) = Nonparametric.comp f_m f_n n_m in
  Filter (f_nm, except_comp n_m ex_m ex_n)

(* Filtering commutes: filtering a dimension by mu and then by sigma yields the same dimension as filtering by sigma and then by mu, regardless of whether mu and sigma are even composable.  Given the mu-filter of b (down to a) and the sigma-filter of b (down to c), this produces the sigma-filter of a and the mu-filter of c, which land on a common dimension e.  TODO: This is currently declared but left unproven (it is a fact about commutativity of generator removal at the except level). *)
type (_, _, _, _, _, _, _, _) filter_comm =
  | Filter_comm :
      ('xs, 'sigma, 'ys, 'e, 'a) filter_dim * ('xm, 'mu, 'ym, 'e, 'c) filter_dim
      -> ('xm, 'mu, 'ym, 'xs, 'sigma, 'ys, 'a, 'c) filter_comm

let filter_comm : type xm mu ym xs sigma ys a b c.
    (xm, mu, ym, a, b) filter_dim ->
    (xs, sigma, ys, c, b) filter_dim ->
    (xm, mu, ym, xs, sigma, ys, a, c) filter_comm =
 fun _ _ -> Sorry.e ()
