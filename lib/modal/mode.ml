open Util
open Signatures
open Dim

(* We want the caller to be able to add new types to the type family Mode.t dynamically, as it reads the user's mode theory.  We could use a generative functor to create those types and an extensible variant to add them to Mode.t, but extensible variants don't play well with Marshall.  Therefore, instead we just use unit all the time, with integers to distinguish modes, and pretend the types are different behind an abstraction barrier. *)

type dummy = private Dummy
type _ t = PK : int -> dummy t

let not_unit : type a b. a t -> (a, unit) Eq.t -> b =
 fun a e ->
  match (a, e) with
  | PK _, _ -> .

let compare : type m n. m t -> n t -> (m, n) Eq.compare =
 fun m n ->
  let PK i, PK j = (m, n) in
  if i = j then Eq else Neq

type wrapped = Wrap : 'mode t -> wrapped

module Mode = struct
  type nonrec 'a t = 'a t

  let compare = compare
end

module Map = struct
  module Key = Mode

  module Make (F : Fam2) = struct
    module Key = Key
    module F = F
    module Internal = Map.Make (Int)

    type 'a t = ('a, dummy) F.t Internal.t

    let empty : type b. b t = Internal.empty

    let find_opt : type g b. g Key.t -> b t -> (b, g) F.t option =
     fun (PK i) m -> Internal.find_opt i m

    let add : type g b. g Key.t -> (b, g) F.t -> b t -> b t = fun (PK i) x m -> Internal.add i x m

    let update : type g b. g Key.t -> ((b, g) F.t option -> (b, g) F.t option) -> b t -> b t =
     fun (PK i) f m -> Internal.update i f m

    let remove : type g b. g Key.t -> b t -> b t = fun (PK i) m -> Internal.remove i m

    type 'a mapper = { map : 'g. 'g Key.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

    let map : type a. a mapper -> a t -> a t =
     fun mapper m -> Internal.mapi (fun i x -> mapper.map (PK i) x) m

    type 'a iterator = { it : 'g. 'g Key.t -> ('a, 'g) F.t -> unit }

    let iter : type a. a iterator -> a t -> unit =
     fun iterator m -> Internal.iter (fun i x -> iterator.it (PK i) x) m
  end
end

module MapCheck : MAP_MAKER with module Key = Mode = Map

module Data = struct
  let names : string Dynarray.t = Dynarray.create ()
  let nonparametric : D.wrapped Dynarray.t = Dynarray.create ()
  let all : (string * wrapped) list ref = ref []
  let unique : wrapped option ref = ref None
end

let all () = !Data.all
let unique () = !Data.unique
let name : type m. m t -> string = fun (PK i) -> Dynarray.get Data.names i
let nonparametric : type m. m t -> D.wrapped = fun (PK i) -> Dynarray.get Data.nonparametric i

let allows_deg : type m n a. a t -> (m, n) deg -> bool =
 fun mode s ->
  let (Wrap d) = degenerated_dims s in
  let (Wrap np) = nonparametric mode in
  let (Except ex) = except_dirs np d in
  match D.compare (excepted ex d) d with
  | Eq -> true
  | Neq -> false

module type Generator = sig
  val name : string

  (* Which directions this mode forbids parametricity in *)
  type nonparametric

  val nonparametric : nonparametric D.t
end

module type Generated = sig
  module G : Generator

  type t

  val mode : t Mode.t
end

module Generate (G : Generator) = struct
  type t = dummy

  let mode : t Mode.t = PK (Dynarray.length Data.names)

  let () =
    Dynarray.add_last Data.names G.name;
    Dynarray.add_last Data.nonparametric (Wrap G.nonparametric);
    Data.all := (G.name, Wrap mode) :: !Data.all;
    Data.unique := if Dynarray.length Data.names = 1 then Some (Wrap mode) else None
end

let generate str =
  let module M = Generate (struct
    let name = str

    type nonparametric = D.zero

    let nonparametric = D.zero
  end) in
  Wrap M.mode
