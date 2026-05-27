open Bwd
open Util
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
    Gen.by_name := StringMap.add G.name (Wrap modality : Gen.all_wrapped) !Gen.by_name
end

type ('src, 'tgt) gen_wrapped = Wrap : ('src, 'morphism, 'tgt) Gen.t -> ('src, 'tgt) gen_wrapped

let generate : type a b. a Mode.t -> b Mode.t -> string -> (a, b) gen_wrapped =
 fun a b c ->
  let module G = struct
    type src = a
    type tgt = b

    let src = a
    let tgt = b
    let name = c
  end in
  let module M = Generate (G) in
  Wrap M.modality

include Path.Make (Gen)
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

(* To be used for debugging only *)
let to_string : type a m b. (a, m, b) t -> string = fun m -> String.concat "" (name m)

(* *)
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
