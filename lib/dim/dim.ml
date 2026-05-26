open Util
module D = D

module Dmap =
  Word.Map
    (Unitcomparable)
    (struct
      module Key = Unitcomparable

      module Make (F : Signatures.Fam2) :
        Signatures.MAP with module Key := Unitcomparable and module F := F = struct
        type 'b t = ('b, unit) F.t option

        let empty : type b. b t = None

        let find_opt : type g b. g Unitcomparable.t -> b t -> (b, g) F.t option =
         fun Unitcomparable.Unit x -> x

        let add : type g b. g Unitcomparable.t -> (b, g) F.t -> b t -> b t =
         fun Unitcomparable.Unit v _ -> Some v

        let update : type g b.
            g Unitcomparable.t -> ((b, g) F.t option -> (b, g) F.t option) -> b t -> b t =
         fun Unitcomparable.Unit f x -> f x

        let remove : type g b. g Unitcomparable.t -> b t -> b t = fun Unit _ -> None

        type 'a mapper = { map : 'g. 'g Unitcomparable.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

        let map : type a. a mapper -> a t -> a t =
         fun f x -> Option.map (f.map Unitcomparable.Unit) x

        type 'a iterator = { it : 'g. 'g Unitcomparable.t -> ('a, 'g) F.t -> unit }

        let iter : type a. a iterator -> a t -> unit =
         fun f x -> Option.iter (f.it Unitcomparable.Unit) x
      end
    end)

let is_pos : type n. n D.t -> bool = function
  | Word Zero -> false
  | Word (Suc _) -> true

module Endpoints = Endpoints
include Singleton
include Deg
include Perm
include Sface
include Bwsface
include Cube
include Tface
include Bwtface
include Tube
include Icube
include Face
include Section
include Op
include Insertion
include Shuffle
include Pbij
module Hott = Hott

type any_dim = Any : 'n D.t -> any_dim

let dim_of_string : string -> any_dim option =
 fun str -> Option.map (fun (Any_deg s) -> Any (dom_deg s)) (deg_of_string str)

let string_of_dim : type n. n D.t -> string = fun n -> string_of_deg (deg_zero n)

(* ********** Special generators ********** *)

let refl : (one, D.zero) deg = Zero D.one

type two = D.two

let sym : (two, two) deg = Suc (Suc (Zero D.zero, Now), Later Now)

let deg_of_name : string -> any_deg option =
 fun str ->
  if List.exists (fun s -> s = str) (Endpoints.refl_names ()) then Some (Any_deg refl)
  else if str = "sym" then Some (Any_deg sym)
  else None

let name_of_deg : type a b.
    sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] -> (a, b) deg -> string option =
 fun ~sort -> function
  | Zero (Word (Suc (Zero, Unit))) -> (
      match (Endpoints.refl_names (), sort) with
      | [], _ -> None
      | _ :: name :: _, (`Type, `Other) -> Some name
      | _ :: _ :: name :: _, (`Function, _) -> Some name
      | _, (`Type, `Canonical) -> None
      | name :: _, _ -> Some name)
  | Suc (Suc (Zero (Word Zero), Now), Later Now) -> Some "sym"
  | _ -> None
