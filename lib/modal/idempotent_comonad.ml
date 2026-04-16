open Util
open Tlist
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
  type comonad = private Dummy_comonad

  type (_, _, _) t =
    | Id_modality : (test_mode, test_mode id_modality, test_mode) t
    | Comonad : ('mode, 'modality, test_mode) t -> ('mode, (comonad, 'modality) cons, test_mode) t

  let rec length : type dom modality cod. (dom, modality, cod) t -> int = function
    | Id_modality -> 0
    | Comonad m -> 1 + length m

  let cod : type a m b. (a, m, b) t -> b Mode.t =
   fun m ->
    match m with
    | Id_modality -> Test_mode
    | Comonad _ -> Test_mode

  let rec dom : type a m b. (a, m, b) t -> a Mode.t =
   fun m ->
    match m with
    | Id_modality -> Test_mode
    | Comonad m -> dom m

  type (_, _) wrapped = Wrap : ('a, 'm, 'b) t -> ('a, 'b) wrapped
  type _ cod_wrapped = Wrap : ('a, 'm, 'b) t -> 'a cod_wrapped
  type _ dom_wrapped = Wrap : ('a, 'm, 'b) t -> 'b dom_wrapped

  let id : type m. m Mode.t -> (m, m id_modality, m) t = function
    | Test_mode -> Id_modality

  type (_, _, _) comp =
    | Id_comp : (test_mode id_modality, 'mu, 'mu) comp
    | Comonad_comp : ('m, 'n, 'mn) comp -> ((comonad, 'm) cons, 'n, (comonad, 'mn) cons) comp

  type (_, _, _, _) composed =
    | Composed : ('a, 'nm, 'b) t * ('n, 'm, 'nm) comp -> ('a, 'n, 'm, 'b) composed

  let rec comp : type a m b n c. (b, n, c) t -> (a, m, b) t -> (a, n, m, c) composed =
   fun m n ->
    match m with
    | Id_modality ->
        let Test_mode = dom n in
        Composed (n, Id_comp)
    | Comonad m ->
        let (Composed (mn, comp)) = comp m n in
        Composed (Comonad mn, Comonad_comp comp)

  let rec comp_uniq : type m n mn1 mn2. (m, n, mn1) comp -> (m, n, mn2) comp -> (mn1, mn2) Eq.t =
   fun m n ->
    match (m, n) with
    | Id_comp, Id_comp -> Eq
    | Comonad_comp m, Comonad_comp n ->
        let Eq = comp_uniq m n in
        Eq

  (* let rec eq_of_comp_id_right : type a m n. (m, a id_modality, n) comp -> (m, n) Eq.t = function
       | Id_comp n ->
           let Id_modality = n in
           Eq
       | Comonad_comp comp ->
           let Eq = eq_of_comp_id_right comp in
           Eq *)

  let eq_of_comp_id_left : type a m n. (a id_modality, m, n) comp -> (m, n) Eq.t = function
    | Id_comp -> Eq

  let rec comp_id_right : type a m b. (a, m, b) t -> (m, a id_modality, m) comp = function
    | Id_modality -> Id_comp
    | Comonad m -> Comonad_comp (comp_id_right m)

  let comp_id_left : type a m b. (a, m, b) t -> (b id_modality, m, m) comp =
   fun m ->
    let Test_mode, Test_mode = (cod m, dom m) in
    Id_comp

  let rec comp_assocl : type m n mn p np mnp.
      (m, n, mn) comp -> (n, p, np) comp -> (m, np, mnp) comp -> (mn, p, mnp) comp =
   fun mn np m_np ->
    match (mn, m_np) with
    | Id_comp, Id_comp -> np
    | Comonad_comp mn, Comonad_comp m_np -> Comonad_comp (comp_assocl mn np m_np)

  let rec comp_assocr : type m n mn p np mnp.
      (m, n, mn) comp -> (n, p, np) comp -> (mn, p, mnp) comp -> (m, np, mnp) comp =
   fun mn np mn_p ->
    match mn with
    | Id_comp ->
        let Eq = comp_uniq np mn_p in
        Id_comp
    | Comonad_comp mn ->
        let (Comonad_comp mn_p) = mn_p in
        let m_np = comp_assocr mn np mn_p in
        Comonad_comp m_np

  let rec compare : type a m b c n d.
      (a, m, b) t -> (c, n, d) t -> (a * m * b, c * n * d) Eq.compare =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Eq
    | Comonad mu, Comonad nu -> (
        match compare mu nu with
        | Eq -> Eq
        | Neq -> Neq)
    | _ -> Neq

  let compare_id : type a m b. (a, m, b) t -> (a * m, b * a id_modality) Eq.compare = function
    | Id_modality -> Eq
    | Comonad _ -> Neq

  let to_colon : type a m b. (a, m, b) t -> [ `Single of string | `Double of string ] = function
    | Id_modality -> `Single ""
    | Comonad _ -> `Double ""

  let to_string : type a m b. (a, m, b) t -> string =
   fun m ->
    match m with
    | Id_modality -> ":"
    | Comonad _ -> "∷" ^ string_of_int (length m)

  let locker : type a. a Mode.t -> (a, a) wrapped = function
    | Test_mode -> Wrap Id_modality

  type (_, _, _, _) factored =
    | Factored : ('b, 'r, 'c) t * ('r, 'n, 'rn) comp -> ('b, 'c, 'n, 'rn) factored

  let rec factor : type a rn b n c. (a, rn, c) t -> (a, n, b) t -> (b, c, n, rn) factored option =
   fun mu nu ->
    match compare mu nu with
    | Eq ->
        let Test_mode = cod mu in
        Some (Factored (Id_modality, comp_id_left nu))
    | Neq -> (
        match (mu, nu) with
        | _, Id_modality -> Some (Factored (mu, comp_id_right mu))
        | Comonad mu, Comonad _ -> (
            match factor mu nu with
            | Some (Factored (pi, comp)) -> Some (Factored (Comonad pi, Comonad_comp comp))
            | None -> None)
        | Id_modality, Comonad _ -> None)

  type (_, _, _, _) pushout =
    | Pushout :
        ('b, 'p, 'd) t * ('c, 'q, 'd) t * ('p, 'm, 'r) comp * ('q, 'n, 'r) comp
        -> ('m, 'n, 'b, 'c) pushout
    | No_pushout

  let pushout : type a b c m n. (a, m, b) t -> (a, n, c) t -> (m, n, b, c) pushout =
   fun m n ->
    match (factor m n, factor n m) with
    | Some (Factored (p, comp)), _ ->
        let Test_mode = cod m in
        Pushout (Id_modality, p, comp_id_left m, comp)
    | _, Some (Factored (q, comp)) ->
        let Test_mode = cod n in
        Pushout (q, Id_modality, comp, comp_id_left n)
    | None, None -> No_pushout

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

  type pre = Id_premodality | Comonad_pre

  let pre_id : pre = Id_premodality

  let of_pre_dom : type a. pre -> a Mode.t -> a cod_wrapped option =
   fun x y ->
    match (x, y) with
    | Id_premodality, Test_mode -> Some (Wrap Id_modality)
    | Comonad_pre, Test_mode -> Some (Wrap (Comonad Id_modality))

  let of_pre_cod : type b. pre -> b Mode.t -> b dom_wrapped option =
   fun x y ->
    match (x, y) with
    | Id_premodality, Test_mode -> Some (Wrap Id_modality)
    | Comonad_pre, Test_mode -> Some (Wrap (Comonad Id_modality))

  let pre_to_colon : pre -> [ `Single of string | `Double of string ] = function
    | Id_premodality -> `Single ""
    | Comonad_pre -> `Double ""

  let pre_to_string : pre -> string = function
    | Id_premodality -> ":"
    | Comonad_pre -> "∷"

  let compare_pre : type dom modality cod. pre -> (dom, modality, cod) t -> bool = fun _ _ -> true

  let compare_pre_id : pre -> bool = function
    | Id_premodality -> true
    | Comonad_pre -> false

  let pre_of_colon : [ `Single of string | `Double of string ] -> pre option = function
    | `Single "" -> Some Id_premodality
    | `Double "" -> Some Comonad_pre
    | _ -> None
end

module Modalcell = struct
  open Modality

  type (_, _, _, _) t =
    | Counit_cell : ('a, 'mu, 'b) Modality.t -> ('a, 'mu, test_mode id_modality, 'b) t
    | Iso_cell :
        ('a, 'mu, test_mode) Modality.t * ('a, 'nu, test_mode) Modality.t
        -> ('a, (comonad, 'mu) cons, (comonad, 'nu) cons, test_mode) t

  (* If there is a unique 2-cell with given domain and codomain, find it.  (Unique cells can be omitted by the user.)  Also checks that the domains and codomains agree. *)
  type (_, _, _, _, _, _) find_unique =
    | Unique : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b, 'a, 'n, 'b) find_unique
    | Nonunique : ('a, 'm, 'b, 'c, 'n, 'd) find_unique

  let find_unique : type a m b c n d.
      (a, m, b) Modality.t -> (c, n, d) Modality.t -> (a, m, b, c, n, d) find_unique =
   fun mu nu ->
    match (mu, nu) with
    | Id_modality, Id_modality -> Unique (Counit_cell Id_modality)
    | Comonad _, Id_modality ->
        let Test_mode = dom mu in
        Unique (Counit_cell mu)
    | Id_modality, Comonad _ -> Nonunique
    | Comonad m', Comonad n' ->
        let Test_mode, Test_mode = (dom mu, dom nu) in
        Unique (Iso_cell (m', n'))

  let id : type dom modality cod.
      (dom, modality, cod) Modality.t -> (dom, modality, modality, cod) t = function
    | Id_modality -> Counit_cell Id_modality
    | Comonad m -> Iso_cell (m, m)

  let id2 : type mode. mode Mode.t -> (mode, mode id_modality, mode id_modality, mode) t = function
    | Test_mode -> Counit_cell Id_modality

  let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
      (dom1, mu1, nu1, cod1) t ->
      (dom2, mu2, nu2, cod2) t ->
      (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
   fun x y ->
    match (x, y) with
    | Counit_cell m, Counit_cell n -> (
        match Modality.compare m n with
        | Eq -> Eq
        | Neq -> Neq)
    | Iso_cell (m, n), Iso_cell (p, q) -> (
        match (Modality.compare m p, Modality.compare n q) with
        | Eq, Eq -> Eq
        | _ -> Neq)
    | _ -> Neq

  let compare_id : type dom mu nu cod.
      (dom, mu, nu, cod) t -> (dom * mu * nu, cod * dom id_modality * dom id_modality) Eq.compare =
    function
    | Counit_cell m -> (
        match Modality.compare_id m with
        | Eq ->
            let Test_mode = dom m in
            Eq
        | Neq -> Neq)
    | Iso_cell _ -> Neq

  type (_, _) wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'b) wrapped
  type (_, _, _) cod_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) cod_wrapped
  type (_, _, _) dom_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) dom_wrapped
  type _ cod2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'a cod2_wrapped
  type _ dom2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'b dom2_wrapped

  let hdom : type a m n b. (a, m, n, b) t -> a Mode.t = function
    | Counit_cell m -> Modality.dom m
    | Iso_cell (m, _) -> Modality.dom m

  let hcod : type a m n b. (a, m, n, b) t -> b Mode.t = function
    | Counit_cell m -> Modality.cod m
    | Iso_cell (m, _) -> Modality.cod m

  let vdom : type a m n b. (a, m, n, b) t -> (a, m, b) Modality.t = function
    | Counit_cell m -> m
    | Iso_cell (m, _) -> Comonad m

  let vcod : type a m n b. (a, m, n, b) t -> (a, n, b) Modality.t = function
    | Counit_cell m ->
        let Test_mode, Test_mode = (dom m, cod m) in
        Id_modality
    | Iso_cell (_, n) -> Comonad n

  let hcomp : type a m n b r s c mr ns.
      (m, r, mr) Modality.comp ->
      (n, s, ns) Modality.comp ->
      (b, m, n, c) t ->
      (a, r, s, b) t ->
      (a, mr, ns, c) t =
   fun mr ns x y ->
    match (x, y) with
    | Counit_cell m, Counit_cell r ->
        let Id_comp = ns in
        let (Composed (mr', comp)) = Modality.comp m r in
        let Eq = Modality.comp_uniq mr comp in
        Counit_cell mr'
    | Iso_cell (m, n), _ ->
        let (Comonad_comp mr') = mr in
        let (Comonad_comp ns') = ns in
        let (Composed (mr'', compr)) = Modality.comp m (vdom y) in
        let (Composed (ns'', comps)) = Modality.comp n (vcod y) in
        let Eq = Modality.comp_uniq mr' compr in
        let Eq = Modality.comp_uniq ns' comps in
        Iso_cell (mr'', ns'')
    | Counit_cell (Comonad m), Iso_cell (r, s) ->
        let Id_comp = ns in
        let (Comonad_comp mr') = mr in
        let (Composed (mr'', comp)) = Modality.comp m (Comonad r) in
        let Eq = Modality.comp_uniq mr' comp in
        Iso_cell (mr'', s)
    | Counit_cell Id_modality, Iso_cell (r, s) ->
        let Id_comp, Id_comp = (mr, ns) in
        Iso_cell (r, s)

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
    | Counit_cell _, _ -> Counit_cell (vdom y)
    | Iso_cell (_, n), Iso_cell (m, _) -> Iso_cell (m, n)

  let vcomp_extending : type a m k kn b n s c.
      (c, k, b) Modality.t ->
      (k, n, kn) Modality.comp ->
      (a, n, s, c) t ->
      (a, m, kn, b) t ->
      (a, m, b) cod_wrapped =
   fun k compn x y ->
    let (Composed (_, comps)) = Modality.comp k (vcod x) in
    let kx = postwhisker compn comps k x in
    Wrap (vcomp kx y)

  let to_string : type a m n b. (a, m, n, b) t -> string =
   fun m ->
    "ε_" ^ string_of_int (Modality.length (vdom m)) ^ "_" ^ string_of_int (Modality.length (vcod m))
end

let test_mode : test_mode Mode.t = Test_mode
let id_modality : (test_mode, test_mode id_modality, test_mode) Modality.t = Id_modality
