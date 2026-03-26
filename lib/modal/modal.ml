open Util
open Signatures
open Dim

type test_mode

module Mode = struct
  type _ t = Test_mode : test_mode t

  let compare : type m n. m t -> n t -> (m, n) Eq.compare =
   fun m n ->
    match (m, n) with
    | Test_mode, Test_mode -> Eq
end

type id_modality

module Modality = struct
  type (_, _, _) t = Id_modality : (test_mode, id_modality, test_mode) t

  let cod : type a m b. (a, m, b) t -> b Mode.t = function
    | Id_modality -> Test_mode

  let dom : type a m b. (a, m, b) t -> a Mode.t = function
    | Id_modality -> Test_mode

  type (_, _) wrapped = Wrap : ('a, 'm, 'b) t -> ('a, 'b) wrapped

  let id : type m. m Mode.t -> (m, m) wrapped = function
    | Test_mode -> Wrap Id_modality

  let comp : type a m b n c. (a, m, b) t -> (b, n, c) t -> (a, c) wrapped =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Wrap Id_modality

  let compare : type a m b c n d. (a, m, b) t -> (c, n, d) t -> (a * m * b, c * n * d) Eq.compare =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Eq

  let compare_id : type a m b. (a, m, b) t -> (a, b) Eq.compare = function
    | Id_modality -> Eq

  let to_string : type a m b. (a, m, b) t -> string = fun _ -> "id"

  let locker : type a. a Mode.t -> (a, a) wrapped = function
    | Test_mode -> Wrap Id_modality

  module Cube (F : Fam3) = struct
    open struct
      type ('a, 'm, 'b) modality_t = ('a, 'm, 'b) t
    end

    type (_, _, _, _) t =
      | Modal :
          ('dom, 'modality, 'mode) modality_t * ('n, ('dom, 'a, 'b) F.t) CubeOf.t
          -> ('n, 'mode, 'a, 'b) t
  end
end

module Modalcell = struct
  type (_, _) t = Id_cell : (id_modality, id_modality) t

  (* If there is a unique 2-cell with given domain and codomain, find it.  (Unique cells can be omitted by the user.)  Also checks that the domains and codomains agree. *)
  type (_, _, _, _, _, _) find_unique =
    | Unique : ('m, 'n) t -> ('a, 'm, 'b, 'a, 'n, 'b) find_unique
    | Nonunique : ('a, 'm, 'b, 'c, 'n, 'd) find_unique

  let find_unique : type a m b c n d.
      (a, m, b) Modality.t -> (c, n, d) Modality.t -> (a, m, b, c, n, d) find_unique =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Unique Id_cell
end

let test_mode : test_mode Mode.t = Test_mode
let id_modality : (test_mode, id_modality, test_mode) Modality.t = Id_modality
