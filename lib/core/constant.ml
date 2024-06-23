open Util

(* This module should not be opened, but be used qualified. *)

(* A constant is identified by an autonumber, scoped by compilation unit. *)
module Constant = struct
  type t = Compunit.t * int

  let compare (x : t) (y : t) = compare x y
end

type t = Constant.t

let counters = Compunit.IntArray.make_basic ()

let make compunit : t =
  let number = Compunit.IntArray.inc counters compunit in
  (compunit, number)

let remake f (c, i) = (f c, i)

(* Data associated to constants is also stored in a map whose domain is their paired identities. *)
module Map = struct
  module IntMap = Map.Make (Int)

  type 'a t = 'a IntMap.t Compunit.Map.t

  let empty : 'a t = Compunit.Map.empty

  let find_opt (i, c) m =
    let open Monad.Ops (Monad.Maybe) in
    let* m = Compunit.Map.find_opt i m in
    IntMap.find_opt c m

  let mem (i, c) m =
    match Compunit.Map.find_opt i m with
    | Some m -> IntMap.mem c m
    | None -> false

  let add (i, c) x m =
    Compunit.Map.update i
      (function
        | None -> Some (IntMap.empty |> IntMap.add c x)
        | Some m -> Some (IntMap.add c x m))
      m

  let update (i, c) f m =
    Compunit.Map.update i
      (function
        | None -> Some (IntMap.update c f IntMap.empty)
        | Some m -> Some (IntMap.update c f m))
      m

  let remove (i, c) m =
    Compunit.Map.update i
      (function
        | None -> None
        | Some m -> Some (IntMap.remove c m))
      m

  let to_channel_unit chan i (m : 'a t) flags =
    Marshal.to_channel chan (Compunit.Map.find_opt i m : 'a IntMap.t option) flags

  let from_channel_unit chan f i (m : 'a t) =
    match (Marshal.from_channel chan : 'a IntMap.t option) with
    | Some x -> Compunit.Map.add i (IntMap.map f x) m
    | None -> m
end
