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
include Cube
include Tface
include Tube
include Icube
include Face
include Section
include Op
include Insertion
include Shuffle
include Pbij
include Except
module Hott = Hott

type any_dim = Any : 'n D.t -> any_dim

let dim_of_string : string -> any_dim option =
 fun str -> Option.map (fun (Any_deg s) -> Any (dom_deg s)) (deg_of_string str)

let string_of_dim : type n. n D.t -> string = fun n -> string_of_deg (deg_zero n)

(* ********** Special generators ********** *)

let refl : (one, D.zero) deg = deg_zero D.one

type two = D.two

let sym : (two, two) deg = deg_suc (deg_suc (deg_zero D.zero) D.deg Now) D.deg (Later Now)

let deg_of_name : string -> any_deg option =
 fun str ->
  if List.exists (fun s -> s = str) (Endpoints.refl_names ()) then Some (Any_deg refl)
  else if str = "sym" then Some (Any_deg sym)
  else None

(* A degeneracy with zero codomain is an iterated reflexivity: it degenerates a zero-dimensional term to some dimension k, which the user can write as k iterated applications of a reflexivity name, like "refl (refl x)" or "Id (Id X)".  (As in strings_of_deg, we assume that all the generators of the domain are reflexivity ones.)  We display it that way only when k is at most the caller-supplied maximum, which the user configures separately for each sort of term with the "display ... degeneracy names" commands; otherwise we fall back on the superscript notation.  Thus name_of_deg returns the number of times its name should be applied, along with that name. *)
let name_of_deg : type a b.
    sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    max:int ->
    (a, b) deg ->
    (string * int) option =
 fun ~sort ~max s ->
  match D.compare_zero (cod_deg s) with
  | Zero -> (
      let k = D.length (dom_deg s) in
      if k < 1 || k > max then None
      else
        match (Endpoints.refl_names (), sort) with
        | [], _ -> None
        | _ :: name :: _, (`Type, `Other) -> Some (name, k)
        | _ :: _ :: name :: _, (`Function, _) -> Some (name, k)
        | _, (`Type, `Canonical) -> None
        | name :: _, _ -> Some (name, k))
  | Pos _ -> (
      match deg_equal s sym with
      | Some () -> Some ("sym", 1)
      | None -> None)
