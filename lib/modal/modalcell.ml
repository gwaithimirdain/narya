open Asai.Range
open Util
open Dim
module StringMap = Map.Make (String)

type ('a, 'm, 'n, 'b) gen =
  | PK : ('a, 'm, 'b) Modality.t * int * ('a, 'n, 'b) Modality.t -> ('a, 'm, 'n, 'b) gen

module Gen = struct
  type ('a, 'm, 'n, 'b) t = ('a, 'm, 'n, 'b) gen
  type all_wrapped = Wrap : ('src, 'm, 'n, 'tgt) gen -> all_wrapped

  let names : string Dynarray.t = Dynarray.create ()
  let by_name : all_wrapped StringMap.t ref = ref StringMap.empty
  let name : type a m n b. (a, m, n, b) t -> string = fun (PK (_, i, _)) -> Dynarray.get names i

  let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
      (dom1, mu1, nu1, cod1) t ->
      (dom2, mu2, nu2, cod2) t ->
      (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
   fun (PK (m, x, n)) (PK (r, y, s)) ->
    match (Modality.compare m r, Modality.compare n s, x = y) with
    | Eq, Eq, true -> Eq
    | _ -> Neq
end

(* All the generating 2-cell names currently in existence, i.e. those of the installed mode theory.  Used for command-line name sanity-checking. *)
let all_names () = Dynarray.to_list Gen.names

let generate : type a m n b.
    string -> (a, m, b) Modality.t -> (a, n, b) Modality.t -> (a, m, n, b) gen =
 fun name m n ->
  let cell = PK (m, Dynarray.length Gen.names, n) in
  Dynarray.add_last Gen.names name;
  Gen.by_name := StringMap.add name (Wrap cell : Gen.all_wrapped) !Gen.by_name;
  cell

type (_, _, _, _) t =
  | Gen : ('a, 'm, 'n, 'b) gen -> ('a, 'm, 'n, 'b) t
  | Id : ('a, 'm, 'b) Modality.t -> ('a, 'm, 'm, 'b) t
  | Hcomp :
      ('a, 'm, 'b, 'r, 'c, 'mr) Modality.comp
      * ('a, 'n, 'b, 's, 'c, 'ns) Modality.comp
      * ('b, 'r, 's, 'c) t
      * ('a, 'm, 'n, 'b) t
      -> ('a, 'mr, 'ns, 'c) t
  | Vcomp : ('a, 'n, 'r, 'b) t * ('a, 'm, 'n, 'b) t -> ('a, 'm, 'r, 'b) t

let of_gen : type a m n b. (a, m, n, b) gen -> (a, m, n, b) t = fun x -> Gen x

(* Change the name of a generating 2-cell, editing its entry in the global names dynarray and by_name map.  Called by the mode theory install functions to implement the command-line flag -modalcells.  Only generating cells can be renamed; passing a composite is a bug in the caller. *)
let rename : type a m n b. (a, m, n, b) t -> string -> unit =
 fun cell name ->
  match cell with
  | Gen (PK (_, i, _) as g) ->
      let old = Dynarray.get Gen.names i in
      Dynarray.set Gen.names i name;
      Gen.by_name := StringMap.remove old !Gen.by_name;
      Gen.by_name := StringMap.add name (Wrap g : Gen.all_wrapped) !Gen.by_name
  | _ -> invalid_arg "Modalcell.rename: not a generating cell"

type (_, _, _, _) adjunction =
  | Adjunction : {
      left : ('a, 'f, 'b) Modality.t;
      right : ('b, 'g, 'a) Modality.t;
      right_left : ('a, 'f, 'b, 'g, 'a, 'gf) Modality.comp;
      unit : ('a, 'a Modality.id, 'gf, 'a) t;
      left_right : ('b, 'g, 'a, 'f, 'b, 'fg) Modality.comp;
      counit : ('b, 'fg, 'b Modality.id, 'b) t;
    }
      -> ('a, 'f, 'g, 'b) adjunction

type (_, _, _) sinister = Sinister : ('a, 'f, 'g, 'b) adjunction -> ('a, 'f, 'b) sinister

(* An adjunction with a specified source mode but everything else existential. *)
type _ any_adjunction = Any_adjunction : ('a, 'f, 'g, 'b) adjunction -> 'a any_adjunction

let id_adjunction : type a. a Mode.t -> (a, a Modality.id, a Modality.id, a) adjunction =
 fun a ->
  let id = Modality.id a in
  Adjunction
    {
      left = id;
      right = id;
      right_left = Modality.comp_id id;
      left_right = Modality.comp_id id;
      unit = Id id;
      counit = Id id;
    }

let id_sinister : type a. a Mode.t -> (a, a Modality.id, a) sinister =
 fun a -> Sinister (id_adjunction a)

(* Accessors for the data of an adjunction. *)
let adj_left : type a f g b. (a, f, g, b) adjunction -> (a, f, b) Modality.t = function
  | Adjunction { left; _ } -> left

let adj_right : type a f g b. (a, f, g, b) adjunction -> (b, g, a) Modality.t = function
  | Adjunction { right; _ } -> right

(* Decide whether an adjunction is the identity adjunction, giving type-level equations if so.  This is used to take fast paths (and preserve pre-modal behavior exactly) for ordinary non-modal fields, which are stored as fields modal over the identity adjunction. *)
let compare_adjunction_id : type a f g b.
    (a, f, g, b) adjunction -> (f * g * b, a Modality.id * a Modality.id * a) Eq.compare = function
  | Adjunction { left; right; _ } -> (
      match Modality.compare_id left with
      | Neq -> Neq
      | Eq -> (
          match Modality.compare_id right with
          | Neq -> Neq
          | Eq -> Eq))

type _ parametric_locker =
  | Locker : ('a, 'm, 'a) Modality.t * ('a, 'm, 'a Modality.id, 'a) t -> 'a parametric_locker

module type Theory = sig
  val sinister : ('a, 'm, 'b) Modality.t -> ('a, 'm, 'b) sinister option
  val compare : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'n, 'b) t -> bool
  val find_unique : ('a, 'm, 'b) Modality.t -> ('a, 'n, 'b) Modality.t -> ('a, 'm, 'n, 'b) t option
  val parametric_locker : 'a Mode.t -> ('a parametric_locker, string) Result.t
  val to_string : ('a, 'm, 'n, 'b) t -> string
end

let theory : (module Theory) ref =
  ref
    (module struct
      let sinister _ = failwith "Modalcell.theory not set"
      let compare _ _ = failwith "Modalcell.theory not set"
      let find_unique _ _ = failwith "Modalcell.theory not set"
      let parametric_locker _ = Error "undefined mode theory"
      let to_string _ = failwith "Modalcell.theory not set"
    end : Theory)

let choose_theory (t : (module Theory)) = theory := t

(* Ask the current theory whether a modality is sinister (a declared left adjoint), obtaining the adjunction data if so. *)
let sinister : type a f b. (a, f, b) Modality.t -> (a, f, b) sinister option =
 fun f ->
  let module T = (val !theory) in
  T.sinister f

type (_, _) wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'b) wrapped
type (_, _, _) cod_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b) cod_wrapped
type (_, _, _) dom_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> ('a, 'n, 'b) dom_wrapped
type _ cod2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'a cod2_wrapped
type _ dom2_wrapped = Wrap : ('a, 'm, 'n, 'b) t -> 'b dom2_wrapped

let rec hsrc : type a m n b. (a, m, n, b) t -> a Mode.t = function
  | Gen (PK (m, _, _)) -> Modality.src m
  | Id m -> Modality.src m
  | Hcomp (_, _, _, x) -> hsrc x
  | Vcomp (_, x) -> hsrc x

let rec htgt : type a m n b. (a, m, n, b) t -> b Mode.t = function
  | Gen (PK (m, _, _)) -> Modality.tgt m
  | Id m -> Modality.tgt m
  | Hcomp (_, _, y, _) -> htgt y
  | Vcomp (_, x) -> htgt x

let rec vsrc : type a m n b. (a, m, n, b) t -> (a, m, b) Modality.t = function
  | Gen (PK (m, _, _)) -> m
  | Id m -> m
  | Hcomp (mr, _, y, _) -> Modality.comp_out (vsrc y) mr
  | Vcomp (_, x) -> vsrc x

let rec vtgt : type a m n b. (a, m, n, b) t -> (a, n, b) Modality.t = function
  | Gen (PK (_, _, n)) -> n
  | Id m -> m
  | Hcomp (_, ns, y, _) -> Modality.comp_out (vtgt y) ns
  | Vcomp (y, _) -> vtgt y

let compare : type dom1 mu1 nu1 cod1 dom2 mu2 nu2 cod2.
    (dom1, mu1, nu1, cod1) t ->
    (dom2, mu2, nu2, cod2) t ->
    (dom1 * mu1 * nu1 * cod1, dom2 * mu2 * nu2 * cod2) Eq.compare =
 fun x y ->
  let module T = (val !theory) in
  match (Modality.compare (vsrc x) (vsrc y), Modality.compare (vtgt x) (vtgt y)) with
  | Eq, Eq -> if T.compare x y then Eq else Neq
  | _ -> Neq

let id : type dom modality cod. (dom, modality, cod) Modality.t -> (dom, modality, modality, cod) t
    =
 fun m -> Id m

let id2 : type mode. mode Mode.t -> (mode, mode Modality.id, mode Modality.id, mode) t =
 fun x -> id (Modality.id x)

let compare_id : type dom mu nu cod.
    (dom, mu, nu, cod) t -> (dom * mu * nu, cod * dom Modality.id * dom Modality.id) Eq.compare =
 fun x ->
  match compare x (id2 (hsrc x)) with
  | Eq -> Eq
  | Neq -> Neq

let hcomp : type a m n b r s c mr ns.
    (a, m, b, r, c, mr) Modality.comp ->
    (a, n, b, s, c, ns) Modality.comp ->
    (b, r, s, c) t ->
    (a, m, n, b) t ->
    (a, mr, ns, c) t =
 fun mr ns x y -> Hcomp (mr, ns, x, y)

let hcomp_wrapped : type a m n b r s c. (b, m, n, c) t -> (a, r, s, b) t -> (a, c) wrapped =
 fun x y ->
  let (Comp mr) = Modality.comp (vsrc y) in
  let (Comp ns) = Modality.comp (vtgt y) in
  Wrap (hcomp mr ns x y)

let postwhisker : type a r s b m c mr ms.
    (a, r, b, m, c, mr) Modality.comp ->
    (a, s, b, m, c, ms) Modality.comp ->
    (b, m, c) Modality.t ->
    (a, r, s, b) t ->
    (a, mr, ms, c) t =
 fun mr ms m x -> hcomp mr ms (id m) x

let postwhisker_wrapped : type a r s b m c. (b, m, c) Modality.t -> (a, r, s, b) t -> (a, c) wrapped
    =
 fun m x -> hcomp_wrapped (id m) x

let prewhisker : type a r b m n c mr nr.
    (a, r, b, m, c, mr) Modality.comp ->
    (a, r, b, n, c, nr) Modality.comp ->
    (b, m, n, c) t ->
    (a, r, b) Modality.t ->
    (a, mr, nr, c) t =
 fun mr nr x m -> hcomp mr nr x (id m)

let prewhisker_wrapped : type a r b m n c. (b, m, n, c) t -> (a, r, b) Modality.t -> (a, c) wrapped
    =
 fun x m -> hcomp_wrapped x (id m)

let rec bprewhisker : type a r b m n c mr nr.
    (a, r, b, m, c, mr) Modality.bcomp ->
    (a, r, b, n, c, nr) Modality.bcomp ->
    (b, m, n, c) t ->
    (a, mr, nr, c) t =
 fun mr nr x ->
  match (mr, nr) with
  | Zero, Zero -> x
  | Suc (g1, mr), Suc (g2, nr) ->
      let Eq = Modality.Gen.src_uniq g1 g2 in
      bprewhisker mr nr
        (prewhisker
           (Suc (Zero, g1))
           (Suc (Zero, g2))
           x
           (Path (Suc (Zero, g2), Modality.Gen.tgt g2)))

let vcomp : type a m n r b. (a, n, r, b) t -> (a, m, n, b) t -> (a, m, r, b) t =
 fun x y -> Vcomp (x, y)

let vcomp_extending : type a m k kn b n s c.
    (c, k, b) Modality.t ->
    (a, n, c, k, b, kn) Modality.comp ->
    (a, n, s, c) t ->
    (a, m, kn, b) t ->
    (a, m, b) cod_wrapped =
 fun k compn x y ->
  let (Comp comps) = Modality.comp (vtgt x) in
  let kx = postwhisker compn comps k x in
  Wrap (vcomp kx y)

type (_, _, _, _, _, _) find_unique =
  | Unique : ('a, 'm, 'n, 'b) t -> ('a, 'm, 'b, 'a, 'n, 'b) find_unique

let find_unique : type a m n b c d.
    (a, m, b) Modality.t -> (c, n, d) Modality.t -> (a, m, b, c, n, d) find_unique option =
 fun m n ->
  let module T = (val !theory) in
  match
    (Mode.compare (Modality.src m) (Modality.src n), Mode.compare (Modality.tgt m) (Modality.tgt n))
  with
  | Eq, Eq -> (
      match T.find_unique m n with
      | Some a -> Some (Unique a)
      | None -> None)
  | _ -> None

let parametric_locker m =
  let module T = (val !theory) in
  if Endpoints.internal () then Locker (Modality.id m, id2 m)
  else
    match T.parametric_locker m with
    | Ok l -> l
    | Error str -> failwith ("mode theory " ^ str ^ " doesn't support external parametricity")

(* Unfortunately, it's not easy for the parser/lexer to store the locations of the individual pieces, so we give them all the location of the entire key. *)
let rec of_name : type mode.
    mode Mode.t ->
    string list located ->
    ( mode cod2_wrapped,
      [ `Not_found of string located | `Wrong_src of Mode.wrapped * string located * Mode.wrapped ]
    )
    Result.t =
 fun mode names ->
  match names.value with
  | [] -> Ok (Wrap (id2 mode))
  | name :: rest -> (
      let go_on : type a m n b.
          (a, m, n, b) t ->
          ( mode cod2_wrapped,
            [ `Not_found of string located
            | `Wrong_src of Mode.wrapped * string located * Mode.wrapped ] )
          Result.t =
       fun cell ->
        match of_name mode (locate_opt names.loc rest) with
        | Ok (Wrap rest) -> (
            match Mode.compare (hsrc cell) (htgt rest) with
            | Eq ->
                let (Wrap output) = hcomp_wrapped cell rest in
                Ok (Wrap output)
            | Neq ->
                Error (`Wrong_src (Wrap (hsrc cell), locate_opt names.loc name, Wrap (htgt rest))))
        | Error e -> Error e in
      match StringMap.find_opt name !Gen.by_name with
      | Some (Wrap cell) -> go_on (of_gen cell)
      | None -> (
          match Modality.of_name_src [ locate_opt names.loc name ] mode with
          | Ok (Wrap m) -> go_on (id m)
          | Error e -> Error e))

let to_string : type a m n b. (a, m, n, b) t -> string =
 fun m ->
  let module T = (val !theory) in
  T.to_string m

(* A "normal form" for a 2-cell, to be printed as a sequence of key applications: a vertical composite (outer list) of horizontal composites / whiskerings (inner list) of key and modality names. *)
type (_, _, _, _) necklace =
  | Necklace_id : 'x Mode.t -> ('x, 'x Modality.id, 'x Modality.id, 'x) necklace
  | Necklace_whisker :
      ('b, 'r, 's, 'c) necklace * ('a, 'm, 'b) Modality.Gen.t
      -> ('a, ('r, 'm) Modality.suc, ('s, 'm) Modality.suc, 'c) necklace
  | Necklace_hcomp :
      ('a, 'm, 'b, 'r, 'c, 'mr) Modality.comp
      * ('a, 'n, 'b, 's, 'c, 'ns) Modality.comp
      * ('b, 'r, 's, 'c) necklace
      * ('a, 'm, 'n, 'b) Gen.t
      -> ('a, 'mr, 'ns, 'c) necklace

let rec necklace_src : type a m n b. (a, m, n, b) necklace -> (a, m, b) Modality.t = function
  | Necklace_id x -> Modality.id x
  | Necklace_whisker (n, g) -> Modality.suc (necklace_src n) g
  | Necklace_hcomp (doms, _, n, _) -> Modality.comp_out (necklace_src n) doms

let rec necklace_tgt : type a m n b. (a, m, n, b) necklace -> (a, n, b) Modality.t = function
  | Necklace_id x -> Modality.id x
  | Necklace_whisker (n, g) -> Modality.suc (necklace_tgt n) g
  | Necklace_hcomp (_, cods, n, _) -> Modality.comp_out (necklace_tgt n) cods

let rec necklace_whisker : type a m b. (a, m, b) Modality.t -> (a, m, m, b) necklace =
 fun m ->
  match m with
  | Path (Zero, x) -> Necklace_id x
  | Path (Suc (m, g), x) -> Necklace_whisker (necklace_whisker (Path (m, x)), g)

let rec necklace_hcomp : type a m n b r s c mr ns.
    (a, m, b, r, c, mr) Modality.comp ->
    (a, n, b, s, c, ns) Modality.comp ->
    (b, r, s, c) necklace ->
    (a, m, n, b) necklace ->
    (a, mr, ns, c) necklace =
 fun doms cods a b ->
  match b with
  | Necklace_id _ ->
      let Zero, Zero = (doms, cods) in
      a
  | Necklace_whisker (b, g) ->
      let Suc (doms, g1), Suc (cods, g2) = (doms, cods) in
      let Eq = Modality.Gen.tgt_uniq g1 g2 in
      let Eq = Modality.Gen.tgt_uniq g g2 in
      Necklace_whisker (necklace_hcomp doms cods a b, g)
  | Necklace_hcomp (bg_doms, bg_cods, b, c) ->
      let (Comp ab_doms) = Modality.comp (necklace_src b) in
      let (Comp ab_cods) = Modality.comp (necklace_tgt b) in
      let ab_g_doms = Modality.comp_assocl ab_doms bg_doms doms in
      let ab_g_cods = Modality.comp_assocl ab_cods bg_cods cods in
      Necklace_hcomp (ab_g_doms, ab_g_cods, necklace_hcomp ab_doms ab_cods a b, c)

let necklace_postwhisker : type a r s b m c mr ms.
    (a, r, b, m, c, mr) Modality.comp ->
    (a, s, b, m, c, ms) Modality.comp ->
    (b, m, c) Modality.t ->
    (a, r, s, b) necklace ->
    (a, mr, ms, c) necklace =
 fun doms cods m n -> necklace_hcomp doms cods (necklace_whisker m) n

let necklace_prewhisker : type a r b m n c mr nr.
    (a, r, b, m, c, mr) Modality.comp ->
    (a, r, b, n, c, nr) Modality.comp ->
    (b, m, n, c) necklace ->
    (a, r, b) Modality.t ->
    (a, mr, nr, c) necklace =
 fun doms cods n m -> necklace_hcomp doms cods n (necklace_whisker m)

let rec necklace_trivial : type a m n b. (a, m, n, b) necklace -> (m, n) Eq.t option = function
  | Necklace_id _ -> Some Eq
  | Necklace_whisker (n, _) -> (
      match necklace_trivial n with
      | Some Eq -> Some Eq
      | None -> None)
  | Necklace_hcomp (_, _, _, _) -> None

(* As we inspect the necklace from right to left (source to target), we accumulate names but also a not-yet-named modality, so that we can pass a maximal modality to Modality.name at once (and get it concatenated to a single string in the one-character case). *)
let rec necklace_name : type x m y n r z.
    (y, n, r, z) necklace -> (x, m, y) Modality.fwd -> string list -> string list =
 fun n m names ->
  match n with
  | Necklace_id _y ->
      (* let (Wrap m) = Modality.of_fwd y m in
         Modality.name m @ names *)
      (* We omit any postwhiskering, since it isn't necessary for re-parsing. *)
      names
  | Necklace_whisker (n, g) -> necklace_name n (Cons (g, m)) names
  | Necklace_hcomp (_, _, n, g) ->
      let (Wrap m) = Modality.of_fwd (hsrc (of_gen g)) m in
      necklace_name n Nil ((Gen.name g :: Modality.name m) @ names)

type (_, _, _, _) nf =
  | Nf_id : ('x, 'm, 'y) Modality.t -> ('x, 'm, 'm, 'y) nf
  | Nf_vcomp : ('a, 'n, 'r, 'b) nf * ('a, 'm, 'n, 'b) necklace -> ('a, 'm, 'r, 'b) nf

let rec nf_vcomp : type a m n r b. (a, n, r, b) nf -> (a, m, n, b) nf -> (a, m, r, b) nf =
 fun a b ->
  match b with
  | Nf_id _ -> a
  | Nf_vcomp (b, n) -> Nf_vcomp (nf_vcomp a b, n)

let rec nf_postwhisker : type a r s b m c mr ms.
    (a, r, b, m, c, mr) Modality.comp ->
    (a, s, b, m, c, ms) Modality.comp ->
    (b, m, c) Modality.t ->
    (a, r, s, b) nf ->
    (a, mr, ms, c) nf =
 fun mr ms m x ->
  match x with
  | Nf_id _ ->
      let Eq = Modality.comp_uniq mr ms in
      Nf_id (Modality.comp_out m mr)
  | Nf_vcomp (x, w) ->
      let (Comp mids) = Modality.comp (necklace_tgt w) in
      Nf_vcomp (nf_postwhisker mids ms m x, necklace_postwhisker mr mids m w)

let rec nf_prewhisker : type a r b m n c mr nr.
    (a, r, b, m, c, mr) Modality.comp ->
    (a, r, b, n, c, nr) Modality.comp ->
    (b, m, n, c) nf ->
    (a, r, b) Modality.t ->
    (a, mr, nr, c) nf =
 fun doms cods a m ->
  match a with
  | Nf_id r ->
      let Eq = Modality.comp_uniq doms cods in
      Nf_id (Modality.comp_out r doms)
  | Nf_vcomp (a, w) ->
      let (Comp mids) = Modality.comp m in
      Nf_vcomp (nf_prewhisker mids cods a m, necklace_prewhisker doms mids w m)

let rec nf_hcomp : type a m n b r s c mr ns.
    (a, m, b, r, c, mr) Modality.comp ->
    (a, n, b, s, c, ns) Modality.comp ->
    (b, r, s, c) nf ->
    (a, m, n, b) nf ->
    (a, mr, ns, c) nf =
 fun doms cods a b ->
  match (a, b) with
  | Nf_id r, Nf_id _ ->
      let Eq = Modality.comp_uniq doms cods in
      Nf_id (Modality.comp_out r doms)
  | Nf_vcomp _, Nf_id m -> nf_prewhisker doms cods a m
  | Nf_id n, Nf_vcomp _ -> nf_postwhisker doms cods n b
  | Nf_vcomp (a, x), Nf_vcomp (b, y) ->
      let (Comp mids) = Modality.comp (necklace_tgt y) in
      Nf_vcomp (nf_hcomp mids cods a b, necklace_hcomp doms mids x y)

(* We call this a "pre-nf" because it hasn't yet had the trivial necklaces removed. *)
let rec pre_nf : type x m n y. (x, m, n, y) t -> (x, m, n, y) nf = function
  | Id m -> Nf_id m
  | Gen g ->
      let m, n = (vsrc (of_gen g), vtgt (of_gen g)) in
      let y = Modality.tgt m in
      Nf_vcomp (Nf_id n, Necklace_hcomp (Modality.id_comp m, Modality.id_comp n, Necklace_id y, g))
  | Hcomp (doms, cods, a, b) ->
      let a, b = (pre_nf a, pre_nf b) in
      nf_hcomp doms cods a b
  | Vcomp (a, b) -> nf_vcomp (pre_nf a) (pre_nf b)

(* This function removes the trivial necklaces. *)
let rec normalize : type x m n y. (x, m, n, y) nf -> (x, m, n, y) nf =
 fun x ->
  match x with
  | Nf_id _ -> x
  | Nf_vcomp (x, w) -> (
      match necklace_trivial w with
      | Some Eq -> normalize x
      | None -> Nf_vcomp (normalize x, w))

let rec nf_name : type x m n y. (x, m, n, y) nf -> string list list -> string list list =
 fun x names ->
  match x with
  | Nf_id _ -> names
  | Nf_vcomp (x, n) -> nf_name x (necklace_name n Nil [] :: names)

let name : type a m n b. (a, m, n, b) t -> string list list =
 fun x -> nf_name (normalize (pre_nf x)) []
