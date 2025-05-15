open Tbwd

(* Map a type-level function. *)
module type TFun = sig
  module Dom : Word.Gen
  module Cod : Word.Gen

  (* We add an extra parameter because we want to get out, in particular, a map of monoid addition parametrized by the thing being added, and once a type is wrapped in a module there's no way to get it out as a parameter. *)
  type 'p param
  type ('p, 'a, 'b) t
  type (_, _) exists = Exists : 'b Cod.t * ('p, 'a, 'b) t -> ('p, 'a) exists

  val exists : 'p param -> 'a Dom.t -> ('p, 'a) exists
  val out : 'p param -> 'a Dom.t -> ('p, 'a, 'b) t -> 'b Cod.t
  val input : 'p param -> 'b Cod.t -> ('p, 'a, 'b) t -> 'a Dom.t
  val uniq : ('p, 'a, 'b1) t -> ('p, 'a, 'b2) t -> ('b1, 'b2) Eq.t
end

module Make (F : TFun) = struct
  module OfDom = Word.Make (F.Dom)
  module OfCod = Word.Make (F.Cod)

  type (_, _, _) t =
    | Map_emp : ('p, emp, emp) t
    | Map_snoc : ('p, 'xs, 'ys) t * ('p, 'x, 'y) F.t -> ('p, ('xs, 'x) snoc, ('ys, 'y) snoc) t

  let rec out : type p xs ys. p F.param -> xs OfDom.t -> (p, xs, ys) t -> ys OfCod.t =
   fun p xs pxs ->
    match (xs, pxs) with
    | Word Zero, Map_emp -> Word Zero
    | Word (Suc (xs, x)), Map_snoc (pxs, px) ->
        let (Word ys) = out p (Word xs) pxs in
        Word (Suc (ys, F.out p x px))

  let rec input : type p xs ys. p F.param -> ys OfCod.t -> (p, xs, ys) t -> xs OfDom.t =
   fun p ys pxs ->
    match (ys, pxs) with
    | Word Zero, Map_emp -> Word Zero
    | Word (Suc (xs, x)), Map_snoc (pxs, px) ->
        let (Word ys) = input p (Word xs) pxs in
        Word (Suc (ys, F.input p x px))

  type (_, _) exists = Exists : 'ys OfCod.t * ('p, 'xs, 'ys) t -> ('p, 'xs) exists

  let rec exists : type p xs. p F.param -> xs OfDom.t -> (p, xs) exists =
   fun p -> function
    | Word Zero -> Exists (Word Zero, Map_emp)
    | Word (Suc (xs, x)) ->
        let (Exists (Word ys, fxs)) = exists p (Word xs) in
        let (Exists (y, fx)) = F.exists p x in
        Exists (Word (Suc (ys, y)), Map_snoc (fxs, fx))

  let rec uniq : type p xs ys zs. (p, xs, ys) t -> (p, xs, zs) t -> (ys, zs) Eq.t =
   fun fxs fxs' ->
    match (fxs, fxs') with
    | Map_emp, Map_emp -> Eq
    | Map_snoc (fxs, fx), Map_snoc (fxs', fx') ->
        let Eq = uniq fxs fxs' in
        let Eq = F.uniq fx fx' in
        Eq

  type (_, _, _, _) insert =
    | Insert : ('zs, 'fx, 'ws) Tbwd.insert * ('p, 'ys, 'ws) t -> ('p, 'fx, 'ys, 'zs) insert

  let rec insert : type p xs x z ys zs.
      (p, x, z) F.t -> (xs, x, ys) Tbwd.insert -> (p, xs, zs) t -> (p, z, ys, zs) insert =
   fun z i fxs ->
    match i with
    | Now -> Insert (Now, Map_snoc (fxs, z))
    | Later i ->
        let (Map_snoc (fxs, fx)) = fxs in
        let (Insert (fi, fxs)) = insert z i fxs in
        Insert (Later fi, Map_snoc (fxs, fx))

  type (_, _, _, _) uninsert =
    | Uninsert :
        ('p, 'x, 'fx) F.t * ('zs, 'fx, 'ws) Tbwd.insert * ('p, 'xs, 'zs) t
        -> ('p, 'x, 'xs, 'ws) uninsert

  let rec uninsert : type p xs x ys ws.
      (xs, x, ys) Tbwd.insert -> (p, ys, ws) t -> (p, x, xs, ws) uninsert =
   fun i fxs ->
    match (fxs, i) with
    | Map_snoc (fxs, fx), Now -> Uninsert (fx, Now, fxs)
    | Map_snoc (fxs, fx), Later i ->
        let (Uninsert (u, fi, fxs)) = uninsert i fxs in
        Uninsert (u, Later fi, Map_snoc (fxs, fx))
    | Map_emp, _ -> .

  type (_, _, _, _) uncoinsert =
    | Uncoinsert :
        ('p, 'x, 'z) F.t * ('xs, 'x, 'ys) Tbwd.insert * ('p, 'xs, 'zs) t
        -> ('p, 'z, 'ys, 'zs) uncoinsert

  let rec uncoinsert : type p ys z zs ws.
      (zs, z, ws) Tbwd.insert -> (p, ys, ws) t -> (p, z, ys, zs) uncoinsert =
   fun i fxs ->
    match i with
    | Now ->
        let (Map_snoc (fxs, fx)) = fxs in
        Uncoinsert (fx, Now, fxs)
    | Later i ->
        let (Map_snoc (fxs, fx)) = fxs in
        let (Uncoinsert (fx', fi, fxs)) = uncoinsert i fxs in
        Uncoinsert (fx', Later fi, Map_snoc (fxs, fx))

  type (_, _, _) map_permute =
    | Map_permute : ('p, 'zs, 'ws) t * ('ys, 'ws) Tbwd.permute -> ('p, 'zs, 'ys) map_permute

  let rec permute : type p xs ys zs.
      (p, xs, ys) t -> (xs, zs) Tbwd.permute -> (p, zs, ys) map_permute =
   fun fxs pp ->
    match pp with
    | Id -> Map_permute (fxs, Id)
    | Insert (pp, i) ->
        let (Map_snoc (fxs, fx)) = fxs in
        let (Map_permute (pfxs, qq)) = permute fxs pp in
        let (Insert (pi, ifx)) = insert fx i pfxs in
        Map_permute (ifx, Insert (qq, pi))
end
