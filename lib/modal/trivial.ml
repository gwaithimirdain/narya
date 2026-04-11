open Util
open Signatures
open Dim

type test_mode = private Dummy_test_mode

module Mode = struct
  type _ t = Test_mode : test_mode t

  module Mode = struct
    type nonrec 'a t = 'a t
  end

  let compare : type m n. m t -> n t -> (m, n) Eq.compare =
   fun m n ->
    match (m, n) with
    | Test_mode, Test_mode -> Eq

  type wrapped = Wrap : 'mode t -> wrapped

  let to_string : type a. a t -> string = function
    | Test_mode -> "Type"

  let all : (string * wrapped) list = [ ("Type", Wrap Test_mode) ]

  (* If there is a unique mode in the present theory, return it. *)
  let unique : unit -> wrapped option = fun () -> Some (Wrap Test_mode)

  module Map : MAP_MAKER with module Key := Mode = struct
    module Key = Mode

    module Make (F : Fam2) = struct
      module F = F

      type 'b t = ('b, test_mode) F.t option

      let empty : 'b t = None

      let find_opt : type m a. m Mode.t -> a t -> (a, m) F.t option = function
        | Test_mode -> fun x -> x

      let add : type m a. m Mode.t -> (a, m) F.t -> a t -> a t = function
        | Test_mode -> fun x _ -> Some x

      let update : type m a. m Mode.t -> ((a, m) F.t option -> (a, m) F.t option) -> a t -> a t =
        function
        | Test_mode -> fun f x -> f x

      let remove : type m b. m Mode.t -> b t -> b t = function
        | Test_mode -> fun _ -> None

      type 'a mapper = { map : 'g. 'g Key.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

      let map : type a. a mapper -> a t -> a t = fun f x -> Option.map (f.map Test_mode) x

      type 'a iterator = { it : 'g. 'g Key.t -> ('a, 'g) F.t -> unit }

      let iter : type a. a iterator -> a t -> unit = fun f x -> Option.iter (f.it Test_mode) x
    end
  end
end

type 'mode id_modality = private Dummy_id_modality

module Modality = struct
  type (_, _, _) t = Id_modality : (test_mode, test_mode id_modality, test_mode) t

  let cod : type a m b. (a, m, b) t -> b Mode.t =
   fun m ->
    match m with
    | Id_modality -> Test_mode

  let dom : type a m b. (a, m, b) t -> a Mode.t =
   fun m ->
    match m with
    | Id_modality -> Test_mode

  type (_, _) wrapped = Wrap : ('a, 'm, 'b) t -> ('a, 'b) wrapped
  type _ cod_wrapped = Wrap : ('a, 'm, 'b) t -> 'a cod_wrapped
  type _ dom_wrapped = Wrap : ('a, 'm, 'b) t -> 'b dom_wrapped

  let id : type m. m Mode.t -> (m, m id_modality, m) t = function
    | Test_mode -> Id_modality

  type (_, _, _) comp =
    | Id_comp : (test_mode id_modality, test_mode id_modality, test_mode id_modality) comp

  type (_, _, _, _) composed =
    | Composed : ('a, 'nm, 'b) t * ('n, 'm, 'nm) comp -> ('a, 'n, 'm, 'b) composed

  let comp : type a m b n c. (b, n, c) t -> (a, m, b) t -> (a, n, m, c) composed =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Composed (Id_modality, Id_comp)

  let eq_of_comp_id_right : type a m n. (m, a id_modality, n) comp -> (m, n) Eq.t = function
    | Id_comp -> Eq

  let eq_of_comp_id_left : type a m n. (a id_modality, m, n) comp -> (m, n) Eq.t = function
    | Id_comp -> Eq

  let comp_id_right : type a m b. (a, m, b) t -> (m, a id_modality, m) comp =
   fun Id_modality -> Id_comp

  let comp_id_left : type a m b. (a, m, b) t -> (b id_modality, m, m) comp =
   fun Id_modality -> Id_comp

  let comp_assocl : type m n mn p np mnp.
      (m, n, mn) comp -> (n, p, np) comp -> (m, np, mnp) comp -> (mn, p, mnp) comp =
   fun mn np m_np ->
    match (mn, np, m_np) with
    | Id_comp, Id_comp, Id_comp -> Id_comp

  let comp_assocr : type m n mn p np mnp.
      (m, n, mn) comp -> (n, p, np) comp -> (mn, p, mnp) comp -> (m, np, mnp) comp =
   fun mn np mn_p ->
    match (mn, np, mn_p) with
    | Id_comp, Id_comp, Id_comp -> Id_comp

  let compare : type a m b c n d. (a, m, b) t -> (c, n, d) t -> (a * m * b, c * n * d) Eq.compare =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Eq

  let compare_id : type a m b. (a, m, b) t -> (a * m, b * a id_modality) Eq.compare = function
    | Id_modality -> Eq

  let to_colon : type a m b. (a, m, b) t -> [ `Single of string | `Double of string ] = function
    | Id_modality -> `Single ""

  let to_string : type a m b. (a, m, b) t -> string = function
    | Id_modality -> ":"

  let locker : type a. a Mode.t -> (a, a) wrapped = function
    | Test_mode -> Wrap Id_modality

  type (_, _, _, _) factored =
    | Factored : ('b, 'r, 'c) t * ('r, 'n, 'rn) comp -> ('b, 'c, 'n, 'rn) factored

  let factor : type a rn b n c. (a, rn, c) t -> (a, n, b) t -> (b, c, n, rn) factored option =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Some (Factored (Id_modality, Id_comp))

  type (_, _, _, _) pushout =
    | Pushout :
        ('b, 'p, 'd) t * ('c, 'q, 'd) t * ('p, 'm, 'r) comp * ('q, 'n, 'r) comp
        -> ('m, 'n, 'b, 'c) pushout
    | No_pushout

  let pushout : type a b c m n. (a, m, b) t -> (a, n, c) t -> (m, n, b, c) pushout =
   fun m n ->
    match (m, n) with
    | Id_modality, Id_modality -> Pushout (Id_modality, Id_modality, Id_comp, Id_comp)

  module Cube (F : Fam3) = struct
    module Parent = struct
      type ('a, 'm, 'b) modality_t = ('a, 'm, 'b) t
    end

    open Parent

    type (_, _, _, _) t =
      | Modal :
          ('dom, 'modality, 'mode) modality_t * ('n, ('dom, 'a, 'b) F.t) CubeOf.t
          -> ('n, 'mode, 'a, 'b) t
  end

  type pre = Id_premodality

  let pre_id : pre = Id_premodality

  let of_pre_dom : type a. pre -> a Mode.t -> a cod_wrapped option =
   fun x y ->
    match (x, y) with
    | Id_premodality, Test_mode -> Some (Wrap Id_modality)

  let of_pre_cod : type b. pre -> b Mode.t -> b dom_wrapped option =
   fun x y ->
    match (x, y) with
    | Id_premodality, Test_mode -> Some (Wrap Id_modality)

  let pre_to_colon : pre -> [ `Single of string | `Double of string ] =
   fun Id_premodality -> `Single ""

  let pre_to_string : pre -> string = fun Id_premodality -> ":"
  let compare_pre : type dom modality cod. pre -> (dom, modality, cod) t -> bool = fun _ _ -> true

  let compare_pre_id : pre -> bool = function
    | Id_premodality -> true

  let pre_of_colon : [ `Single of string | `Double of string ] -> pre option = function
    | `Single "" -> Some Id_premodality
    | _ -> None
end

module Modalcell = struct
  type (_, _, _, _) t =
    | Id_cell : (test_mode, test_mode id_modality, test_mode id_modality, test_mode) t

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

  let id2 : type mode. mode Mode.t -> (mode, mode id_modality, mode id_modality, mode) t = function
    | Test_mode -> Id_cell

  let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
      (dom1, mu1, nu1, cod1) t ->
      (dom2, mu2, nu2, cod2) t ->
      (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
   fun x y ->
    match (x, y) with
    | Id_cell, Id_cell -> Eq

  let compare_id : type dom mu nu cod.
      (dom, mu, nu, cod) t -> (dom * mu * nu, cod * dom id_modality * dom id_modality) Eq.compare =
    function
    | Id_cell -> Eq

  type (_, _) wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'b) wrapped
  type (_, _, _) cod_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) cod_wrapped
  type (_, _, _) dom_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) dom_wrapped
  type _ cod2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'a cod2_wrapped
  type _ dom2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'b dom2_wrapped

  let hdom : type a m n b. (a, m, n, b) t -> a Mode.t = function
    | Id_cell -> Test_mode

  let hcod : type a m n b. (a, m, n, b) t -> b Mode.t = function
    | Id_cell -> Test_mode

  let vdom : type a m n b. (a, m, n, b) t -> (a, m, b) Modality.t = function
    | Id_cell -> Id_modality

  let vcod : type a m n b. (a, m, n, b) t -> (a, n, b) Modality.t = function
    | Id_cell -> Id_modality

  let hcomp : type a m n b r s c mr ns.
      (m, r, mr) Modality.comp ->
      (n, s, ns) Modality.comp ->
      (b, m, n, c) t ->
      (a, r, s, b) t ->
      (a, mr, ns, c) t =
   fun mr ns x y ->
    match (mr, ns, x, y) with
    | Id_comp, Id_comp, Id_cell, Id_cell -> Id_cell

  let hcomp_wrapped : type a m n b r s c. (b, m, n, c) t -> (a, r, s, b) t -> (a, c) wrapped =
   fun x y ->
    let (Composed (_, mr)) = Modality.comp (vdom x) (vdom y) in
    let (Composed (_, ns)) = Modality.comp (vcod x) (vcod y) in
    Wrap (hcomp mr ns x y)

  let postwhisker : type a r s b m c mr ms.
      (m, r, mr) Modality.comp ->
      (m, s, ms) Modality.comp ->
      (b, m, c) Modality.t ->
      (a, r, s, b) t ->
      (a, mr, ms, c) t =
   fun mr ms m x -> hcomp mr ms (id m) x

  let postwhisker_wrapped : type a r s b m c.
      (b, m, c) Modality.t -> (a, r, s, b) t -> (a, c) wrapped =
   fun m x -> hcomp_wrapped (id m) x

  let prewhisker : type a r b m n c mr nr.
      (m, r, mr) Modality.comp ->
      (n, r, nr) Modality.comp ->
      (b, m, n, c) t ->
      (a, r, b) Modality.t ->
      (a, mr, nr, c) t =
   fun mr nr x m -> hcomp mr nr x (id m)

  let prewhisker_wrapped : type a r b m n c.
      (b, m, n, c) t -> (a, r, b) Modality.t -> (a, c) wrapped =
   fun x m -> hcomp_wrapped x (id m)

  let vcomp : type a m n r b. (a, n, r, b) t -> (a, m, n, b) t -> (a, m, r, b) t =
   fun x y ->
    match (x, y) with
    | Id_cell, Id_cell -> Id_cell

  let vcomp_extending : type a m k kn b n s c.
      (k, n, kn) Modality.comp -> (a, n, s, c) t -> (a, m, kn, b) t -> (a, m, c) cod_wrapped =
   fun comp x y ->
    match (comp, x, y) with
    | Id_comp, Id_cell, Id_cell -> Wrap Id_cell

  let to_string : type a m n b. (a, m, n, b) t -> string = fun Id_cell -> "id"
end

let test_mode : test_mode Mode.t = Test_mode
let id_modality : (test_mode, test_mode id_modality, test_mode) Modality.t = Id_modality
