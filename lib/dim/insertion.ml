open Util
open Tlist
open Tbwd
open Signatures
open Sface
open Tface
open Deg
open Perm

(* An element of ('a, 'b, 'c) insertion is an insertion of 'c into 'b: a permutation from a to b+c that maintains the relative order of 'b.  *)
(* TODO: Should an insertion be parametrized by b+c as well? *)
type (_, _, _) insertion =
  | Zero : 'a D.t -> ('a, 'a, D.zero) insertion
  | Suc :
      ('a, 'b, 'c) insertion * 'g D.G.t * ('a, 'g, 'asuc) D.insert
      -> ('asuc, 'b, ('c, 'g) D.suc) insertion

let ins_zero : type a. a D.t -> (a, a, D.zero) insertion = fun a -> Zero a

let eq_of_ins_zero : type a b. (a, b, D.zero) insertion -> (a, b) Eq.t = function
  | Zero _ -> Eq

let rec zero_ins : type a. a D.t -> (a, D.zero, a) insertion =
 fun a ->
  match a with
  | Word Zero -> Zero a
  | Word (Suc (a, g)) ->
      let ins = zero_ins (Word a) in
      Suc (ins, g, Now)

let rec id_ins : type a b ab. a D.t -> (a, b, ab) D.plus -> (ab, a, b) insertion =
 fun a b ->
  match b with
  | Zero -> Zero a
  | Suc (b, g) ->
      let ins = id_ins a b in
      Suc (ins, g, Now)

let rec dom_ins : type a b c. (a, b, c) insertion -> a D.t = function
  | Zero a -> a
  | Suc (ins, g, i) -> D.insert i (dom_ins ins) g

let rec cod_left_ins : type a b c. (a, b, c) insertion -> b D.t = function
  | Zero a -> a
  | Suc (ins, _, _) -> cod_left_ins ins

let rec cod_right_ins : type a b c. (a, b, c) insertion -> c D.t = function
  | Zero _ -> D.zero
  | Suc (ins, g, _) -> D.suc (cod_right_ins ins) g

let rec equal_ins : type a1 b1 c1 a2 b2 c2.
    (a1, b1, c1) insertion -> (a2, b2, c2) insertion -> unit option =
 fun i1 i2 ->
  match (i1, i2) with
  | Zero a1, Zero a2 -> (
      match D.compare a1 a2 with
      | Eq -> Some ()
      | Neq -> None)
  | Suc (i1, g1, x1), Suc (i2, g2, x2) -> (
      match D.G.compare g1 g2 with
      | Neq -> None
      | Eq -> (
          match D.insert_equiv x1 x2 with
          | None -> None
          | Some () -> equal_ins i1 i2))
  | _ -> None

let rec plus_ins : type a b c d ab ac.
    a D.t -> (a, b, ab) D.plus -> (a, c, ac) D.plus -> (b, c, d) insertion -> (ab, ac, d) insertion
    =
 fun a ab ac ins ->
  match ins with
  | Zero _ ->
      let Eq = D.plus_uniq ab ac in
      Zero (D.plus_out a ab)
  | Suc (ins, g, i) ->
      let (Plus ab') = D.plus (D.uninsert i (D.plus_right ab)) in
      Suc (plus_ins a ab' ac ins, g, D.plus_insert ab' ab i)

(* If a+b=ab, then there is an identity permutation that inserts b on the right of a. *)
let rec ins_of_plus : type a b ab. a D.t -> (a, b, ab) D.plus -> (ab, a, b) insertion =
 fun a ab ->
  match ab with
  | Zero -> Zero a
  | Suc (ab, g) -> Suc (ins_of_plus a ab, g, Now)

(* An insertion induces a degeneracy, which is in fact a permutation. *)
let rec deg_of_ins_plus : type a b c bc. (a, b, c) insertion -> (b, c, bc) D.plus -> (a, bc) deg =
 fun i bc ->
  match (i, bc) with
  | Zero a, Zero -> id_deg a
  | Suc (i, g, e), Suc (bc, _) -> Suc (deg_of_ins_plus i bc, g, e)

let deg_of_ins : type a b c. (a, b, c) insertion -> a deg_to =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  To (deg_of_ins_plus ins bc)

let rec perm_of_ins_plus : type a b c bc. (a, b, c) insertion -> (b, c, bc) D.plus -> (a, bc) perm =
 fun i bc ->
  match (i, bc) with
  | Zero a, Zero -> id_perm a
  | Suc (i, g, e), Suc (bc, _) -> Suc (perm_of_ins_plus i bc, g, e)

let perm_of_ins : type a b c. (a, b, c) insertion -> a perm_to =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  Perm_to (perm_of_ins_plus ins bc)

let rec is_id_ins : type a b c. (a, b, c) insertion -> (b, c, a) D.plus option = function
  | Zero _ -> Some Zero
  | Suc (ins, g, Now) -> (
      match is_id_ins ins with
      | Some bc -> Some (Suc (bc, g))
      | None -> None)
  | Suc (_, _, Later _) -> None

let deg_of_plus_of_ins : type a b c. (a, b, c) insertion -> b deg_of_plus =
 fun ins ->
  let (Plus bc) = D.plus (cod_right_ins ins) in
  Of (bc, deg_of_ins_plus ins bc)

(* Any degeneracy with a decomposition of its codomain factors as an insertion followed by a whiskered degeneracy.  The whiskered degeneracy does all the permutation of 'a and inserting degenerate dimensions into it, and then the insertion puts 'c back in the corresponding places. *)

type (_, _, _) insfact = Insfact : ('a, 'b) deg * ('ac, 'a, 'c) insertion -> ('ac, 'b, 'c) insfact

let rec insfact : type ac b c bc. (ac, bc) deg -> (b, c, bc) D.plus -> (ac, b, c) insfact =
 fun s bc ->
  match bc with
  | Zero -> Insfact (s, Zero (dom_deg s))
  | Suc (bc, _) ->
      let (Suc (s, g, e)) = s in
      let (Insfact (s, i)) = insfact s bc in
      Insfact (s, Suc (i, g, e))

(* In particular, since an insertion induces a degeneracy (a permutation) with a decomposition of its codomain, if we compose a degeneracy followed by an insertion, the result factors in the above way as an insertion followed by a whiskered degeneracy. *)

type (_, _, _) insfact_comp =
  | Insfact_comp : ('k, 'm) deg * ('kn, 'k, 'n) insertion -> ('m, 'n, 'kn) insfact_comp

let insfact_comp : type m n mn kn. (mn, m, n) insertion -> (kn, mn) deg -> (m, n, kn) insfact_comp =
 fun ins s ->
  let (Plus mn) = D.plus (cod_right_ins ins) in
  let (Insfact (fc, ins)) = insfact (comp_deg (deg_of_ins_plus ins mn) s) mn in
  Insfact_comp (fc, ins)

(* Here is version that also allows the given degeneracy to have any domain and codomain, and do the composition by extending both with identities as in comp_deg_extending. *)

type (_, _, _) insfact_comp_ext =
  | Insfact_comp_ext :
      ('m, 'n) deg * ('ml, 'm, 'l) insertion * ('k, 'j, 'l) D.plus * ('a, 'i, 'ml) D.plus
      -> ('n, 'k, 'a) insfact_comp_ext

let insfact_comp_ext : type n k nk a b.
    (nk, n, k) insertion -> (a, b) deg -> (n, k, a) insfact_comp_ext =
 fun ins s ->
  let (Plus nk) = D.plus (cod_right_ins ins) in
  let s' = deg_of_ins_plus ins nk in
  let (DegExt (ai, nk_d, s's)) = comp_deg_extending s' s in
  let (Plus kd) = D.plus (D.plus_right nk_d) in
  let n_kd = D.plus_assocr nk kd nk_d in
  let (Insfact (fa, new_ins)) = insfact s's n_kd in
  Insfact_comp_ext (fa, new_ins, kd, ai)

(* A strict face of the left codomain of an insertion can be extended to a strict face of its domain, completing a commutative square with a larger insertion. *)

type (_, _, _) sface_lift_ins =
  | Sface_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) sface -> ('m, 'k, 'nk) sface_lift_ins

let rec sface_lift_ins : type n k nk m.
    (m, n) sface -> (nk, n, k) insertion -> (m, k, nk) sface_lift_ins =
 fun fa0 ins0 ->
  match ins0 with
  | Zero _ -> Sface_lift_ins (Zero (dom_sface fa0), fa0)
  | Suc (ins1, g1, i1) ->
      let (Sface_lift_ins (ins2, fa1)) = sface_lift_ins fa0 ins1 in
      let (Insert_sface (j2, fa2)) = insert_sface fa1 g1 i1 in
      Sface_lift_ins (Suc (ins2, g1, j2), fa2)

(* Or a proper face *)

type (_, _, _) pface_lift_ins =
  | Pface_lift_ins : ('mk, 'm, 'k) insertion * ('mk, 'nk) pface -> ('m, 'k, 'nk) pface_lift_ins

let rec pface_lift_ins : type n k nk m.
    (m, n) pface -> (nk, n, k) insertion -> (m, k, nk) pface_lift_ins =
 fun fa0 ins0 ->
  match ins0 with
  | Zero _ -> Pface_lift_ins (Zero (dom_tface fa0), fa0)
  | Suc (ins1, g1, i1) ->
      let (Pface_lift_ins (ins2, fa1)) = pface_lift_ins fa0 ins1 in
      let (Insert_pface (j2, fa2)) = insert_pface fa1 g1 i1 in
      Pface_lift_ins (Suc (ins2, g1, j2), fa2)

(* Construct an insertion from a domain and a list of numbers. *)
type _ ins_of = Ins_of : ('ab, 'a, 'b) insertion -> 'ab ins_of

let rec ins_of_ints : type ab. ab D.t -> int list -> ab ins_of option =
 fun ab ns ->
  match ns with
  | [] -> Some (Ins_of (Zero ab))
  | n :: ns -> (
      match D.insert_of_int ab (n - 1) with
      | Some (Into (g, ix)) -> (
          try
            let ns =
              List.map
                (fun i ->
                  if i < n then i
                  else if i > n then i - 1
                  else raise (Invalid_argument "ins_of_ints"))
                ns in
            match ins_of_ints (D.uninsert ix ab) ns with
            | Some (Ins_of ins) -> Some (Ins_of (Suc (ins, g, ix)))
            | None -> None
          with Invalid_argument _ -> None)
      | None -> None)

(* Conversely, display an insertion as a list of numbers. *)
let rec ints_of_ins : type ab a b. (ab, a, b) insertion -> int list = function
  | Zero _ -> []
  | Suc (ins, _, ix) ->
      let x = Tbwd.int_of_insert ix + 1 in
      x :: List.map (fun i -> if i >= x then i + 1 else i) (ints_of_ins ins)

let string_of_ins_ints : int list -> string =
 fun ints ->
  let strs = List.map string_of_int ints in
  if List.is_empty strs then ""
  else if List.fold_right (fun s m -> max (String.length s) m) strs 0 > 1 then
    ".." ^ String.concat "." strs
  else "." ^ String.concat "" strs

let string_of_ins : type ab a b. (ab, a, b) insertion -> string =
 fun ins -> string_of_ins_ints (ints_of_ins ins)

type any_ins = Any_ins : ('a, 'b, 'c) insertion -> any_ins

(* List all the insertions with a given total dimension. *)
let rec all_ins_of : type ab. ab D.t -> ab ins_of Seq.t =
 fun ab ->
  let open Monad.Ops (Monad.Seq) in
  Seq.cons (Ins_of (Zero ab))
    (let* (Into (g, ix)) = D.all_inserts ab in
     let* (Ins_of ins) = all_ins_of (D.uninsert ix ab) in
     return (Ins_of (Suc (ins, g, ix))))

(* Intrinsically well-typed maps.  This is basically a simplified version of Pbijmap where the 'remaining is always equal to 0, and hence is not a parameter.  This means we don't actually need the functorial parametrization either, as the simple version InsmapOf is sufficient for all uses.  But we keep it in case later we want to parametrize the values by the 'shared as well.  We do still need a recursive module, since we are still doing a mutual recursion with the functor Tuple. *)

module rec Internal_Insmap : functor (F : Fam) -> sig
  module Param : sig
    type (_, _, _) t =
      | Match :
          ('evaluation, 'intrinsic, 'v) Internal_Insmap(F).t
          -> ('g, 'evaluation, ('g * 'intrinsic) * 'v) t
      | Mismatch : ('g, 'g0) D.G.apart -> ('g, 'evaluation, ('g0 * 'intrinsic) * 'v) t
  end

  module Tup : module type of Tuple.Make (D.G) (Param)

  type (_, _, _) t =
    | Zero : 'v F.t -> ('evaluation, D.zero, 'v) t
    | Suc :
        'g D.G.t * ('evaluation, ('g * 'intrinsic) * 'v) Tup.t
        -> ('evaluation, ('intrinsic, 'g) D.suc, 'v) t
end =
functor
  (F : Fam)
  ->
  struct
    (* The values stored in the tuple of subtrees are gated by the generator of the tuple position: a subtree exists only at positions whose generator matches that of the intrinsic dimension being shared there (as the Match constructor's index records), while mismatched positions store only an apartness witness, which lookups eliminate statically since their key types entail the contradictory equality.  This makes the maps marshallable, since no closures are stored. *)
    module Param = struct
      type (_, _, _) t =
        | Match :
            ('evaluation, 'intrinsic, 'v) Internal_Insmap(F).t
            -> ('g, 'evaluation, ('g * 'intrinsic) * 'v) t
        | Mismatch : ('g, 'g0) D.G.apart -> ('g, 'evaluation, ('g0 * 'intrinsic) * 'v) t
    end

    module Tup = Tuple.Make (D.G) (Param)

    (* In the absence of the 'remaining parametrization, we don't need a "gt" version but can go right to the "t". *)
    type (_, _, _) t =
      | Zero : 'v F.t -> ('evaluation, D.zero, 'v) t
      | Suc :
          'g D.G.t * ('evaluation, ('g * 'intrinsic) * 'v) Tup.t
          -> ('evaluation, ('intrinsic, 'g) D.suc, 'v) t
  end

module Insmap (F : Fam) = struct
  include Internal_Insmap (F)

  type (_, _) wrapped = Wrap : ('evaluation, 'intrinsic, 'v) t -> ('evaluation, 'v) wrapped

  let rec find : type evaluation intrinsic shared v.
      (evaluation, shared, intrinsic) insertion -> (evaluation, intrinsic, v) t -> v F.t =
   fun p m ->
    match (p, m) with
    | Zero _, Zero v -> v
    | Suc (ins, _, i), Suc (_, m) -> (
        (* The Mismatch case is statically unreachable in the current single-generator instantiation (apart is empty), but is genuine multi-generator logic, so we keep it and silence the unreachability warning. *)
        (match Tup.find i m with
        | Match m -> find ins m
        | Mismatch ap -> (
            match D.G.apart_irrefl ap with
            | _ -> .))
        [@warning "-56"])

  let rec set : type evaluation intrinsic shared v.
      (evaluation, shared, intrinsic) insertion ->
      v F.t ->
      (evaluation, intrinsic, v) t ->
      (evaluation, intrinsic, v) t =
   fun p v m ->
    match (p, m) with
    | Zero _, Zero _ -> Zero v
    | Suc (ins, _, i), Suc (g0, m) ->
        Suc
          ( g0,
            Tup.update i
              ((function
                | Match m -> Match (set ins v m)
                | Mismatch ap -> (
                    match D.G.apart_irrefl ap with
                    | _ -> .)) [@warning "-56"])
              m )

  let find_singleton : type evaluation intrinsic v. (evaluation, intrinsic, v) t -> v F.t option =
    function
    | Zero v -> Some v
    | Suc _ -> None

  type ('evaluation, 'intrinsic, 'v) builder = {
    build : 'shared. ('evaluation, 'shared, 'intrinsic) insertion -> 'v F.t;
  }

  let rec build : type evaluation intrinsic v.
      evaluation D.t ->
      intrinsic D.t ->
      (evaluation, intrinsic, v) builder ->
      (evaluation, intrinsic, v) t =
   fun evaluation intrinsic f ->
    let (Word iplus) = intrinsic in
    match iplus with
    | Zero -> Zero (f.build (ins_zero evaluation))
    | Suc (type i1 g0t) ((intrinsic, g0) : (_, i1, _) D.plus * g0t D.G.t) ->
        let f : type b h.
            h D.G.t -> (b, h, evaluation) Tbwd.insert -> (h, b, (g0t * i1) * v) Param.t =
         fun h i ->
          (match D.G.decide h g0 with
          | Same ->
              Match
                (build (D.uninsert i evaluation) (Word intrinsic)
                   { build = (fun ins -> f.build (Suc (ins, g0, i))) })
          | Distinct ap -> Mismatch ap)
          [@warning "-56"] in
        Suc (g0, Tup.build evaluation { build = f })

  let singleton : type evaluation v. v F.t -> (evaluation, D.zero, v) t = fun v -> Zero v

  (* Generic traversal *)

  module Times = struct
    type (_, _, _) t = Times : ('p, 'x, 'p * 'x) t
    type (_, _) exists = Exists : ('p, 'a, 'b) t -> ('p, 'a) exists

    let exists : ('p, 'a) exists = Exists Times
  end

  module MapTimes = Tlist.Map (Times)

  module Heter = struct
    type _ hft = [] : nil hft | ( :: ) : 'v F.t * 'vs hft -> ('v, 'vs) cons hft

    type (_, _, _) ht =
      | [] : ('e, 'i, nil) ht
      | ( :: ) : ('e, 'i, 'v) t * ('e, 'i, 'vs) ht -> ('e, 'i, ('v, 'vs) cons) ht

    let rec zero : type e vs. vs hft -> (e, D.zero, vs) ht = function
      | [] -> []
      | v :: vs -> Zero v :: zero vs

    let rec suc : type e i g vs irvs.
        g D.G.t ->
        (g * i, vs, irvs) MapTimes.t ->
        (e, nil, irvs) Tup.Heter.hgt ->
        (e, (i, g) D.suc, vs) ht =
     fun g irvs rs ->
      match (irvs, rs) with
      | [], [] -> []
      | Times :: irvs, right :: rs -> Suc (g, right) :: suc g irvs rs

    let rec zeros : type e vs. (e, D.zero, vs) ht -> vs hft = function
      | [] -> []
      | Zero v :: ms -> v :: zeros ms

    let rec right : type e i g vs irvs.
        (e, (i, g) D.suc, vs) ht -> (g * i, vs, irvs) MapTimes.t -> (e, nil, irvs) Tup.Heter.hgt =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | Suc (_, r) :: ms, Times :: irvs -> r :: right ms irvs

    let rec wrap : type e i g vs irvs.
        (e, i, vs) ht -> (g * i, vs, irvs) MapTimes.t -> (g, e, irvs) Tup.Heter.hft =
     fun ms irvs ->
      match (ms, irvs) with
      | [], [] -> []
      | m :: ms, Times :: irvs -> Match m :: wrap ms irvs

    let rec unwrap : type e i g vs irvs.
        (g, e, irvs) Tup.Heter.hft -> (g * i, vs, irvs) MapTimes.t -> (e, i, vs) ht =
     fun ms irvs ->
      (match (ms, irvs) with
      | [], [] -> []
      | Match m :: ms, Times :: irvs -> m :: unwrap ms irvs
      | Mismatch ap :: _, Times :: _ -> (
          match D.G.apart_irrefl ap with
          | _ -> .))
      [@warning "-56"]

    (* For tuple positions whose generator is apart from the map's intrinsic generator, the values just record the apartness witness. *)
    let rec mismatched : type e g g0 i vs irvs.
        (g, g0) D.G.apart -> (g0 * i, vs, irvs) MapTimes.t -> (g, e, irvs) Tup.Heter.hft =
     fun ap irvs ->
      match irvs with
      | [] -> []
      | Times :: irvs -> Mismatch ap :: mismatched ap irvs

    let rec params : type e i vs. (e, i, vs) ht -> vs Tlist.t = function
      | [] -> Nil
      | _ :: vs -> Cons (params vs)
  end

  module Infix = struct
    let hnil : nil Heter.hft = []
    let ( @: ) : type x xs. x F.t -> xs Heter.hft -> (x, xs) cons Heter.hft = fun x xs -> x :: xs
  end

  open Infix

  module Applicatic (M : Applicative.Plain) = struct
    open Applicative.Ops (M)

    type ('evaluation, 'intrinsic, 'vs, 'ws) pmapperM = {
      map :
        'shared. ('evaluation, 'shared, 'intrinsic) insertion -> 'vs Heter.hft -> 'ws Heter.hft M.t;
    }

    let rec pmapM : type evaluation intrinsic v vs ws.
        evaluation D.t ->
        (evaluation, intrinsic, (v, vs) cons, ws) pmapperM ->
        (evaluation, intrinsic, (v, vs) cons) Heter.ht ->
        ws Tlist.t ->
        (evaluation, intrinsic, ws) Heter.ht M.t =
     fun evaluation f ms ws ->
      match ms with
      | Zero _ :: _ ->
          M.apply (f.map (ins_zero evaluation) (Heter.zeros ms)) @@ fun res -> Heter.zero res
      | Suc (g0, _) :: _ -> pmapM_suc evaluation g0 f ms ws

    and pmapM_suc : type evaluation i1 g0t v vs ws.
        evaluation D.t ->
        g0t D.G.t ->
        (evaluation, (i1, g0t) D.suc, (v, vs) cons, ws) pmapperM ->
        (evaluation, (i1, g0t) D.suc, (v, vs) cons) Heter.ht ->
        ws Tlist.t ->
        (evaluation, (i1, g0t) D.suc, ws) Heter.ht M.t =
     fun evaluation g0 f ms ws ->
      let module T = Tup.Applicatic (M) in
      let (Exists_cons irvs) = MapTimes.exists_cons (Heter.params ms) in
      let irvs : (g0t * i1, (v, vs) cons, _) MapTimes.t = irvs in
      let (Exists irws) = MapTimes.exists ws in
      let irws : (g0t * i1, ws, _) MapTimes.t = irws in
      let map : type a g.
          g D.G.t ->
          (a, g, evaluation) Tbwd.insert ->
          (g, a, _) Tup.Heter.hft ->
          (g, a, _) Tup.Heter.hft M.t =
       fun g i x ->
        (match D.G.decide g g0 with
        | Same ->
            (* The equation g = g0t lets us view this position's data at the map's generator. *)
            let x : (g0t, a, _) Tup.Heter.hft = x in
            let i : (a, g0t, evaluation) Tbwd.insert = i in
            M.apply
              (pmapM (D.uninsert i evaluation)
                 { map = (fun ins v -> f.map (Suc (ins, g0, i)) v) }
                 (Heter.unwrap x irvs) ws)
            @@ fun res -> Heter.wrap res irws
        | Distinct ap -> return (Heter.mismatched ap irws))
        [@warning "-56"] in
      M.apply (T.pmapM { map } (Heter.right ms irvs) (MapTimes.cod irws)) @@ fun rights ->
      Heter.suc g0 irws rights

    type ('evaluation, 'intrinsic, 'vs, 'w) mmapperM = {
      map : 'shared. ('evaluation, 'shared, 'intrinsic) insertion -> 'vs Heter.hft -> 'w F.t M.t;
    }

    let mmapM e f xs =
      M.apply
        (pmapM e { map = (fun i x -> M.apply (f.map i x) @@ fun y -> y @: hnil) } xs (Cons Nil))
      @@ fun [ ys ] -> ys

    type ('evaluation, 'intrinsic, 'vs) miteratorM = {
      it : 'shared. ('evaluation, 'shared, 'intrinsic) insertion -> 'vs Heter.hft -> unit M.t;
    }

    let miterM e f xs =
      M.apply (pmapM e { map = (fun i x -> M.apply (f.it i x) @@ fun () -> hnil) } xs Nil)
      @@ fun [] -> ()
  end

  module Monadic (M : Monad.Plain) = struct
    module A = Applicative.OfMonad (M)
    include Applicatic (A)
  end

  module IdM = Monadic (Monad.Identity)

  let pmap f xs qs = IdM.pmapM f xs qs
  let mmap f xs = IdM.mmapM f xs
  let miter f xs = IdM.miterM f xs
end

module InsmapOf = Insmap (struct
  type 'b t = 'b
end)
