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

  let to_string : type a. a t -> string = fun _ -> "Type"
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

  let comp : type a m b n c. (b, n, c) t -> (a, m, b) t -> (a, c) wrapped =
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

  let factor : type a m b n c. (a, m, c) t -> (a, n, b) t -> (b, c) wrapped =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Wrap Id_modality

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
  type (_, _, _, _) t = Id_cell : (test_mode, id_modality, id_modality, test_mode) t

  (* If there is a unique 2-cell with given domain and codomain, find it.  (Unique cells can be omitted by the user.)  Also checks that the domains and codomains agree. *)
  type (_, _, _, _, _, _) find_unique =
    | Unique : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b, 'a, 'n, 'b) find_unique
    | Nonunique : ('a, 'm, 'b, 'c, 'n, 'd) find_unique

  let find_unique : type a m b c n d.
      (a, m, b) Modality.t -> (c, n, d) Modality.t -> (a, m, b, c, n, d) find_unique =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Unique Id_cell

  let id : type dom modality cod.
      (dom, modality, cod) Modality.t -> (dom, modality, modality, cod) t = function
    | Id_modality -> Id_cell

  let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
      (dom1, mu1, nu1, cod1) t ->
      (dom2, mu2, nu2, cod2) t ->
      (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
   fun x y ->
    match (x, y) with
    | Id_cell, Id_cell -> Eq

  let compare_id : type dom mu nu cod. (dom, mu, nu, cod) t -> (dom * mu, cod * nu) Eq.compare =
    function
    | Id_cell -> Eq

  type (_, _) wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'b) wrapped

  let hdom : type a m n b. (a, m, n, b) t -> a Mode.t = function
    | Id_cell -> Test_mode

  let hcod : type a m n b. (a, m, n, b) t -> b Mode.t = function
    | Id_cell -> Test_mode

  let vdom : type a m n b. (a, m, n, b) t -> (a, m, b) Modality.t = function
    | Id_cell -> Id_modality

  let vcod : type a m n b. (a, m, n, b) t -> (a, n, b) Modality.t = function
    | Id_cell -> Id_modality

  let hcomp : type a m n b r s c. (b, m, n, c) t -> (a, r, s, b) t -> (a, c) wrapped =
   fun x y ->
    match (x, y) with
    | Id_cell, Id_cell -> Wrap Id_cell

  let postwhisker : type a r s b m c. (b, m, c) Modality.t -> (a, r, s, b) t -> (a, c) wrapped =
   fun m x -> hcomp (id m) x

  let prewhisker : type a r b m n c. (b, m, n, c) t -> (a, r, b) Modality.t -> (a, c) wrapped =
   fun x m -> hcomp x (id m)

  let vcomp : type a m n r b. (a, n, r, b) t -> (a, m, n, b) t -> (a, m, r, b) t =
   fun x y ->
    match (x, y) with
    | Id_cell, Id_cell -> Id_cell

  type (_, _, _) with_dom = With_dom : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) with_dom

  let vcomp_extending : type a m nn b n s c. (a, m, nn, b) t -> (a, n, s, c) t -> (a, m, c) with_dom
      =
   fun x y ->
    match (x, y) with
    | Id_cell, Id_cell -> With_dom Id_cell
end

let test_mode : test_mode Mode.t = Test_mode
let id_modality : (test_mode, id_modality, test_mode) Modality.t = Id_modality
