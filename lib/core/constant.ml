(* This module should not be opened, but be used qualified. *)

open Util
open Origin

(* A constant is identified by an autonumber, scoped by an Origin. *)
module Constant = struct
  type t = Origin.t * int

  let compare (x : t) (y : t) = compare x y
end

type t = Constant.t

(* Store autonumber counters *)
let counters = Versioned.make ~default:(fun _ -> 0) ~inherit_values:false

(* Create a new constant in the current execution location (file or interactive instant). *)
let make () : t =
  let current = Origin.current () in
  let number = Versioned.get counters in
  Versioned.set counters (number + 1);
  (current, number)

(* Recreate a constant with an altered file identifier, as when linking. *)
let remake f ((c : Origin.t), i) =
  match c with
  | File n -> (Origin.File (f n), i)
  (* Built-in constants should be created in the same order with the same identifiers in every execution run, so we don't need to change them. *)
  | Top -> (c, i)
  | Instant _ -> raise (Failure "Constant: can't remake interactive constant")

(* A constant Table is mutable and versioned, and can store any kind of data. *)
module Table = struct
  module IntMap = Map.Make (Int)

  type 'a t = 'a IntMap.t Versioned.t

  let make () = Versioned.make ~default:(fun () -> IntMap.empty) ~inherit_values:false
  let find_opt (c, i) tbl = Option.bind (Versioned.get_at tbl c) (IntMap.find_opt i)

  let add (c, i) v tbl =
    if c = Origin.current () then Versioned.set tbl (IntMap.add i v (Versioned.get tbl))
    else raise (Failure "Constant.Table: can only add to the current origin")

  (* Get or set all the data associated to a single file. *)

  type 'a origin_entry = 'a IntMap.t option

  let find_file file tbl = Versioned.get_at tbl (File file)

  let add_file file x tbl =
    match x with
    | Some x -> Versioned.set_file tbl file x
    | None -> ()

  (* Marshal the objects associated to a specific origin only. *)
  let to_channel_origin chan origin (tbl : 'a t) flags =
    Marshal.to_channel chan (Versioned.get_at tbl origin) flags

  (* Unmarshal the objects associated to a specific origin only, applying f to their elements before adding them to the current map, and returning the new origin data. *)
  let from_istream_origin chan f origin tbl =
    match (Istream.unmarshal chan : 'a IntMap.t option) with
    | Some x ->
        let fx = IntMap.map f x in
        Option.bind (Versioned.set_at tbl origin fx) @@ fun () -> Some fx
    | None -> None
end

(* Other data associated to constants is stored in a Map whose domain is their paired identities.  This doesn't record any history, so it should generally only be used locally to a particular instant. *)
module Map = Map.Make (Constant)
