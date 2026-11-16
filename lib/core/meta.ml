(* This module should not be opened, but used qualified. *)

open Util
open Signatures
open Modal
open Energy
open Origin
open Tctx

(* Metavariables, such as holes and unification variables.  Local generative definitions are also reperesented as metavariables.  A metavariable is identified by its class, an autonumber that's specific to the class, and its origin (file or interactive instant).  Since the autonumbers are specific to the class, we store them as arguments of the class, even though every metavariable has one. *)

(* A defined metavariable is either bound by a let or let rec, or else inserted automatically to hold the value of a case tree construct (such as a match, comatch, or canonical type) appearing bare in a kinetic position, in which case we record what sort of construct it was. *)
type sort = [ `Let | `Letrec of letrec_block | `Bare of string ]

(* The metavariables bound by the same "let rec … and …" block share a block identifier. *)
and letrec_block = int

let string_of_sort : sort -> string = function
  | `Let -> "let"
  | `Letrec _ -> "letrec"
  | `Bare sort -> sort

module Identity = struct
  type t = [ `Hole of int | `Def of int * sort ]

  let compare : t -> t -> int = compare
end

(* A metavariable is also parametrized by its raw context length, its checked context length, and its energy (kinetic or potential), although these are not part of its identity.  We store witnesses of these so that we can compare them to make the type parameters match up; all the other properties of a metavariable are stored in its definition (see Metadef). *)
module Extended_identity = struct
  type ('mode, 'a, 'b, 's) t = {
    identity : Identity.t;
    mode : 'mode Mode.t;
    raw : 'a N.t;
    len : ('mode, 'b) Tctx.t;
    energy : 's energy;
  }

  let compare : type m1 m2 a1 b1 s1 a2 b2 s2.
      (m1, a1, b1, s1) t -> (m2, a2, b2, s2) t -> (m1 * a1 * b1 * s1, m2 * a2 * b2 * s2) Eq.compare
      =
   fun x y ->
    (* We compare the identities first, since comparing the lengths takes time linear in them. *)
    if x.identity <> y.identity then Neq
    else
      match
        ( Mode.compare x.mode y.mode,
          N.compare x.raw y.raw,
          Tctx.compare x.len y.len,
          Energy.compare x.energy y.energy )
      with
      | Eq, Eq, Eq, Eq -> Eq
      | _ -> Neq
end

(* Finally, a metavariable as stored elsewhere in the code also knows its origin.  We don't store origins as part of the extended identity because the metavariable tables that look things up by extended identity are versioned, so origins are stored as part of the versioning process. *)
type ('mode, 'a, 'b, 's) t = Origin.t * ('mode, 'a, 'b, 's) Extended_identity.t

(* Make metavariables of each class. *)

(* Store autonumber counters for defined metavariables, for both files and instants. *)
let def_counters = Versioned.make ~default:(fun _ -> 0) ~inherit_values:false

(* Store autonumber counters for "let rec" blocks, similarly. *)
let block_counters = Versioned.make ~default:(fun _ -> 0) ~inherit_values:false

let new_letrec_block () : letrec_block =
  let number = Versioned.get block_counters in
  Versioned.set block_counters (number + 1);
  number

(* The constant whose definition is currently being checked, if any, which will be the owner of any metavariables created (see Metadef). *)
module Owner = Algaeff.Reader.Make (struct
  type t = Constant.t option
end)

let () = Owner.register_printer (function `Read -> Some "unhandled Meta.Owner effect")

(* Install the handler for the owner effect, with no owner.  This is done once at top level. *)
let run_owner : type x. (unit -> x) -> x = fun f -> Owner.run ~env:None f

let with_owner_opt : type x. Constant.t option -> (unit -> x) -> x =
 fun owner f -> Owner.run ~env:owner f

let with_owner : type x. Constant.t -> (unit -> x) -> x =
 fun const f -> with_owner_opt (Some const) f

let current_owner () = Owner.read ()

(* For each owner, the local names that have been given to its metavariables.  Like the definitions of constants, this is versioned, so that it is backtracked when speculation fails (see Origin.speculate) and on undo; thus a binding that is checked more than once gets the same name each time. *)
module StringSet = Set.Make (String)

let local_names : StringSet.t Constant.Table.t = Constant.Table.make ()

let owner_local_name : Constant.t -> string -> string =
 fun const name ->
  let used = Option.value ~default:StringSet.empty (Constant.Table.find_opt const local_names) in
  let rec until_unique k =
    let namek = name ^ Unicode.primes k in
    if StringSet.mem namek used then until_unique (k + 1) else namek in
  let local = until_unique 0 in
  Constant.Table.add const (StringSet.add local used) local_names;
  local

(* The local name to give a new defined metavariable bound to a variable with a given name, if any: if it has an owner, the name is made unique among the metavariables of that owner by adding primes. *)
let local_name : string option -> string option =
 fun name ->
  match (Owner.read (), name) with
  | Some const, Some name -> Some (owner_local_name const name)
  | _ -> name

(* Create a new defined metavariable in the current execution location (file or interactive instant). *)
let make_def : type mode a b s.
    sort -> mode Mode.t -> a N.t -> (mode, b) Tctx.t -> s energy -> (mode, a, b, s) t =
 fun sort mode raw len energy ->
  let origin = Origin.current () in
  let number = Versioned.get def_counters in
  Versioned.set def_counters (number + 1);
  let identity = `Def (number, sort) in
  (origin, { identity; mode; raw; len; energy })

(* We just use one global hole counter, so that a hole can be represented by a single number to communicate with the user and ProofGeneral.  But to make up for that, we have to remember the origin of each hole as a function of its global number.  Note that this dynarray never shrinks, so old holes that have gone away are still here.  There wouldn't be any easy way to do that, since solving an old hole can create new holes that have to be at the end of the array, so the origins don't appear here in order. *)
let hole_origins : Origin.t Dynarray.t = Dynarray.create ()

(* We record the next hole number separately with a Speculable, so that speculatively created holes don't increment it. *)
let next_hole : int Speculable.t = Speculable.make 0

let make_hole : type mode a b s.
    mode Mode.t -> a N.t -> (mode, b) Tctx.t -> s energy -> (mode, a, b, s) t =
 fun mode raw len energy ->
  let origin = Origin.current () in
  let number = Speculable.get next_hole in
  Speculable.set next_hole (number + 1);
  while Dynarray.length hole_origins <= number do
    Dynarray.add_last hole_origins origin
  done;
  Dynarray.set hole_origins number origin;
  let identity = `Hole number in
  (origin, { identity; mode; raw; len; energy })

(* Re-make (link) a metavariable when loading a compiled version from disk. *)
let remake : type mode a b s. (File.t -> File.t) -> (mode, a, b, s) t -> (mode, a, b, s) t =
 fun f (origin, m) ->
  match origin with
  | Top -> raise (Failure "can't remake built-in metavariable")
  | File file -> (File (f file), m)
  | Instant _ -> raise (Failure "can't remake interactive metavariable")

(* Printable names. *)
let mode : type mode a b s. (mode, a, b, s) t -> mode Mode.t = fun (_, m) -> m.mode

(* A defined metavariable bound to a named variable is named like "foo.bar._baz", where "foo.bar" is the name of its owner, as computed by the supplied function, and "baz" its local name.  If it has no owner, or the function isn't supplied, then the owner is replaced by its origin and autonumber, as in "F3.17._baz".  A defined metavariable not bound to a named variable, such as one inserted automatically to hold a bare case tree construct, is named like "foo.bar.__match.F3.17", with its sort, origin, and autonumber.  The owner and local name are stored in the definition of the metavariable, so they have to be supplied (see Global.meta_name). *)
let name : type mode a b s.
    ?owner_name:(Constant.t -> string) ->
    ?owner:Constant.t ->
    ?local:string ->
    (mode, a, b, s) t ->
    string =
 fun ?owner_name ?owner ?local (origin, x) ->
  match x.identity with
  | `Hole number ->
      (* We don't need to include the origin here, since holes are sequentially numbered globally rather than by origin. *)
      Printf.sprintf "?%d" number
  | `Def (number, sort) -> (
      let owner =
        match (owner_name, owner) with
        | Some owner_name, Some owner -> Some (owner_name owner)
        | _ -> None in
      let numbered = Printf.sprintf "%s.%d" (Origin.to_string origin) number in
      match (owner, local) with
      | Some owner, Some local -> Printf.sprintf "%s._%s" owner local
      | None, Some local -> Printf.sprintf "%s._%s" numbered local
      | Some owner, None -> Printf.sprintf "%s.__%s.%s" owner (string_of_sort sort) numbered
      | None, None -> Printf.sprintf "__%s.%s" (string_of_sort sort) numbered)

(* The sort of a defined metavariable, if it is one. *)
let sort_of : type mode a b s. (mode, a, b, s) t -> sort option =
 fun (_, x) ->
  match x.identity with
  | `Def (_, sort) -> Some sort
  | `Hole _ -> None

(* Whether a metavariable was inserted automatically to hold a bare case tree construct. *)
let is_bare : type mode a b s. (mode, a, b, s) t -> bool =
 fun (_, x) ->
  match x.identity with
  | `Def (_, `Bare _) -> true
  | `Def (_, (`Let | `Letrec _)) | `Hole _ -> false

(* Whether two metavariables were bound by the same "let rec" block. *)
let letrec_siblings : type m1 a1 b1 s1 m2 a2 b2 s2. (m1, a1, b1, s1) t -> (m2, a2, b2, s2) t -> bool
    =
 fun (origin1, x1) (origin2, x2) ->
  origin1 = origin2
  &&
  match (x1.identity, x2.identity) with
  | `Def (_, `Letrec block1), `Def (_, `Letrec block2) -> block1 = block2
  | _ -> false

let origin : type mode a b s. (mode, a, b, s) t -> Origin.t = fun (origin, _) -> origin

(* Compare two metavariables for equality, returning equality of their lengths and energies. *)
let compare : type m1 m2 a1 b1 s1 a2 b2 s2.
    (m1, a1, b1, s1) t -> (m2, a2, b2, s2) t -> (m1 * a1 * b1 * s1, m2 * a2 * b2 * s2) Eq.compare =
 fun (x_origin, x) (y_origin, y) ->
  match (x_origin = y_origin, Extended_identity.compare x y) with
  | true, Eq -> Eq
  | _ -> Neq

type wrapped = Wrap : ('mode, 'a, 'b, 's) t -> wrapped

module Wrapped = struct
  type t = wrapped

  let compare : t -> t -> int =
   fun (Wrap (_, x)) (Wrap (_, y)) -> Identity.compare x.identity y.identity
end

module WrapSet = Set.Make (Wrapped)
module WrapMap = Map.Make (Wrapped)

(* Representation of holes for interacting with ProofGeneral. *)
let hole_number : type mode a b s. (mode, a, b, s) t -> int =
 fun (_, m) ->
  match m.identity with
  | `Hole number -> number
  | _ -> raise (Failure "not an interactive hole")

(* A metavariable table, like a constant table, is MUTABLE and versioned, and can store anything.  It is also intrinsically well-typed, with values that can be parametrized by the raw length, checked length, and energy of the metavariable.  We don't store it using any fancy maps, though: just an ordinary map over the unparametrized identity with all the type parameters stored existentially, and we test equality of the parametrizing types when performing operations. *)

module IdMap = Map.Make (Identity)

module Table = struct
  type ('mode, 'a, 'b, 's) key = ('mode, 'a, 'b, 's) t

  module Make (F : Fam5) = struct
    type _ entry =
      | Entry : ('mode, 'a, 'b, 's) Extended_identity.t * ('x, 'mode, 'a, 'b, 's) F.t -> 'x entry

    type 'x t = 'x entry IdMap.t Versioned.t

    let make () = Versioned.make ~default:(fun () -> IdMap.empty) ~inherit_values:false

    let find_opt : type mode x a b s. (mode, a, b, s) key -> x t -> (x, mode, a, b, s) F.t option =
     fun (origin, key) m ->
      (* Apparently we can't use Monad.Ops(Monad.Maybe) here because the type doesn't get sufficiently refined. *)
      match Versioned.get_at m origin with
      | Some m -> (
          match IdMap.find_opt key.identity m with
          | None -> None
          | Some (Entry (key', value)) -> (
              match Extended_identity.compare key key' with
              | Eq -> Some value
              | Neq -> raise (Failure "Meta.Map.find_opt")))
      | None -> None

    type _ hole = Hole : ('mode, 'a, 'b, 's) key * ('x, 'mode, 'a, 'b, 's) F.t -> 'x hole

    let find_hole_opt : type x. int -> x t -> x hole option =
     fun i m ->
      try
        let c = Dynarray.get hole_origins i in
        match Versioned.get_at m c with
        | Some m ->
            Option.bind (IdMap.find_opt (`Hole i) m) @@ fun (Entry (m, v)) ->
            Some (Hole ((c, m), v))
        | None -> None
      with Invalid_argument _ -> None

    let add : type x mode a b s. (mode, a, b, s) key -> (x, mode, a, b, s) F.t -> x t -> unit =
     fun (origin, key) value m ->
      if origin = Origin.current () then
        let a = Option.value ~default:IdMap.empty (Versioned.get_at m origin) in
        let newa = IdMap.add key.identity (Entry (key, value)) a in
        Versioned.set m newa
      else raise (Failure "Meta.Table: can only add to the current origin")

    type ('x, 'acc) folder = {
      fold : 'mode 'a 'b 's. ('mode, 'a, 'b, 's) key -> ('x, 'mode, 'a, 'b, 's) F.t -> 'acc -> 'acc;
    }

    let fold : type x acc. (x, acc) folder -> x t -> acc -> acc =
     fun f m acc ->
      let go acc origin m =
        IdMap.fold (fun _ (Entry (key, value)) acc -> f.fold (origin, key) value acc) m acc in
      Versioned.foldi m go acc

    let fold_current : type x acc. (x, acc) folder -> x t -> acc -> acc =
     fun f m acc ->
      IdMap.fold
        (fun _ (Entry (key, value)) acc -> f.fold (Origin.current (), key) value acc)
        (Versioned.get m) acc

    type 'x origin_entry = 'x entry IdMap.t option

    let find_file (file : File.t) (m : 'a t) = Versioned.get_at m (File file)

    let add_file file x m =
      match x with
      | Some x -> Versioned.set_file m file x
      | None -> ()

    let to_channel_origin : type x.
        Out_channel.t -> Origin.t -> x t -> Marshal.extern_flags list -> unit =
     fun chan origin m flags -> Marshal.to_channel chan (Versioned.get_at m origin) flags

    type 'x mapper = {
      map :
        'mode 'a 'b 's.
        ('mode, 'a, 'b, 's) key -> ('x, 'mode, 'a, 'b, 's) F.t -> ('x, 'mode, 'a, 'b, 's) F.t;
    }

    let from_istream_origin : type x. Istream.t -> x mapper -> Origin.t -> x t -> x origin_entry =
     fun chan f origin m ->
      match (Istream.unmarshal chan : x origin_entry) with
      | Some n ->
          let fn =
            IdMap.map (fun (Entry (key, value)) -> Entry (key, f.map (origin, key) value)) n in
          Option.bind (Versioned.set_at m origin fn) @@ fun () -> Some fn
      | None -> None
  end
end
