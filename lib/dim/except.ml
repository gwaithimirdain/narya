open Util
open Tbwd
open Sface
open Deg
open Perm

(* ********** Omitting directions ********** *)

(* ('e, 'a, 'b) except means that 'a is obtained from 'b by omitting all occurrences of any directions appearing in 'e. *)

type (_, _, _) except =
  | Except_zero : ('e, D.zero, D.zero) except
  | Except_occurs : ('e, 'a, 'b) except * ('g, 'e) D.occurs -> ('e, 'a, ('b, 'g) snoc) except
  | Except_unoccurs :
      ('e, 'a, 'b) except * ('g, 'e) D.unoccurs
      -> ('e, ('a, 'g) snoc, ('b, 'g) snoc) except

let rec excepted : type e a b. (e, a, b) except -> b D.t -> a D.t =
 fun ex b ->
  match (ex, b) with
  | Except_zero, Word Zero -> Word Zero
  | Except_occurs (ex, _), Word (Suc (b, _)) -> excepted ex (Word b)
  | Except_unoccurs (ex, _), Word (Suc (b, g)) ->
      let (Word a) = excepted ex (Word b) in
      Word (Suc (a, g))

type (_, _) has_except = Except : ('e, 'a, 'b) except -> ('e, 'b) has_except

let rec except_dirs : type e b. e D.t -> b D.t -> (e, b) has_except =
 fun e -> function
  | Word Zero -> Except Except_zero
  | Word (Suc (b, h)) -> (
      let (Except ex) = except_dirs e (Word b) in
      match D.occurs h e with
      | Left o -> Except (Except_occurs (ex, o))
      | Right u -> Except (Except_unoccurs (ex, u)))

let rec except_uniq : type e a1 a2 b. (e, a1, b) except -> (e, a2, b) except -> (a1, a2) Eq.t =
 fun e1 e2 ->
  match (e1, e2) with
  | Except_zero, Except_zero -> Eq
  | Except_occurs (e1, _), Except_occurs (e2, _) ->
      let Eq = except_uniq e1 e2 in
      Eq
  | Except_unoccurs (e1, _), Except_unoccurs (e2, _) ->
      let Eq = except_uniq e1 e2 in
      Eq
  | Except_occurs (_, o), Except_unoccurs (_, u) -> D.occurs_unoccurs o u
  | Except_unoccurs (_, u), Except_occurs (_, o) -> D.occurs_unoccurs o u

let except_zero : ('e, D.zero, D.zero) except = Except_zero

let rec except_nothing : type a. a D.t -> (D.zero, a, a) except = function
  | Word Zero -> Except_zero
  | Word (Suc (a, _)) -> Except_unoccurs (except_nothing (Word a), Unoccurs_emp)

let rec eq_of_except_nothing : type a b. (D.zero, a, b) except -> (a, b) Eq.t = function
  | Except_zero -> Eq
  | Except_unoccurs (e, _) ->
      let Eq = eq_of_except_nothing e in
      Eq
  | Except_occurs (_, _) -> .

let rec except_idempotent : type e a b. (e, a, b) except -> (e, a, a) except = function
  | Except_zero -> Except_zero
  | Except_occurs (e, _) -> except_idempotent e
  | Except_unoccurs (e, u) -> Except_unoccurs (except_idempotent e, u)

let rec except_plus : type e a b c d ac bd.
    (a, c, ac) D.plus ->
    (b, d, bd) D.plus ->
    (e, a, b) except ->
    (e, c, d) except ->
    (e, ac, bd) except =
 fun ac bd eab ecd ->
  match (bd, ecd) with
  | Zero, Except_zero ->
      let Zero = ac in
      eab
  | Suc (bd, _), Except_occurs (ecd, o) -> Except_occurs (except_plus ac bd eab ecd, o)
  | Suc (bd, _), Except_unoccurs (ecd, u) ->
      let (Suc (ac, _)) = ac in
      Except_unoccurs (except_plus ac bd eab ecd, u)

type (_, _, _, _) except_of_plus =
  | Except_of_plus :
      ('a, 'c, 'ac) D.plus * ('e, 'a, 'b) except * ('e, 'c, 'd) except
      -> ('e, 'b, 'd, 'ac) except_of_plus

let rec except_of_plus : type e b d ac bd.
    (b, d, bd) D.plus -> (e, ac, bd) except -> (e, b, d, ac) except_of_plus =
 fun bd eacbd ->
  match (bd, eacbd) with
  | Zero, _ -> Except_of_plus (Zero, eacbd, Except_zero)
  | Suc (bd, _), Except_occurs (eacbd, o) ->
      let (Except_of_plus (ac, eab, ecd)) = except_of_plus bd eacbd in
      Except_of_plus (ac, eab, Except_occurs (ecd, o))
  | Suc (bd, g), Except_unoccurs (eacbd, u) ->
      let (Except_of_plus (ac, eab, ecd)) = except_of_plus bd eacbd in
      Except_of_plus (Suc (ac, g), eab, Except_unoccurs (ecd, u))

type (_, _, _, _) except_of_plus' =
  | Except_of_plus' :
      ('b, 'c, 'bc) D.plus * ('bc, 'd) perm * ('e, 'a, 'b) except
      -> ('e, 'a, 'c, 'd) except_of_plus'

let rec except_of_plus' : type a c ac e d.
    d D.t -> (a, c, ac) D.plus -> (e, ac, d) except -> (e, a, c, d) except_of_plus' =
 fun d ac e ->
  match (e, d, ac) with
  | _, _, Zero -> Except_of_plus' (Zero, id_perm d, e)
  | Except_unoccurs (e, _), Word (Suc (d, Unit)), Suc (ac, _) ->
      let (Except_of_plus' (bc, p, e)) = except_of_plus' (Word d) ac e in
      Except_of_plus' (Suc (bc, Unit), Suc (p, Now), e)
  | Except_occurs (e, Occurs i), Word (Suc (d, Unit)), _ ->
      let (Except_of_plus' (bc, p, e)) = except_of_plus' (Word d) ac e in
      ignore (i, bc, p, e);
      Sorry.e ()

type (_, _, _) except_sface =
  | Except_sface : ('d, 'a) sface * ('e, 'd, 'c) except -> ('e, 'a, 'c) except_sface

let rec except_sface : type e a b c. (e, a, b) except -> (c, b) sface -> (e, a, c) except_sface =
 fun e s ->
  match (e, s) with
  | Except_zero, Zero -> Except_sface (Zero, Except_zero)
  | Except_occurs (e, _), End (s, _) -> except_sface e s
  | Except_occurs (e, o), Mid s ->
      let (Except_sface (s, e)) = except_sface e s in
      Except_sface (s, Except_occurs (e, o))
  | Except_unoccurs (e, _), End (s, l) ->
      let (Except_sface (s, e)) = except_sface e s in
      Except_sface (End (s, l), e)
  | Except_unoccurs (e, u), Mid s ->
      let (Except_sface (s, e)) = except_sface e s in
      Except_sface (Mid s, Except_unoccurs (e, u))

let rec except_occurs_insert : type e a b g c.
    (e, a, b) except -> (b, g, c) Tbwd.insert -> (g, e) D.occurs -> (e, a, c) except =
 fun e i occ ->
  match i with
  | Now -> Except_occurs (e, occ)
  | Later i -> (
      match e with
      | Except_occurs (e, o) -> Except_occurs (except_occurs_insert e i occ, o)
      | Except_unoccurs (e, u) -> Except_unoccurs (except_occurs_insert e i occ, u))

type (_, _, _, _) except_unoccurs_insert =
  | Except_unoccurs_insert :
      ('a, 'g, 'ag) Tbwd.insert * ('e, 'ag, 'c) except
      -> ('e, 'a, 'g, 'c) except_unoccurs_insert

let rec except_unoccurs_insert : type e a b g c.
    (e, a, b) except ->
    (b, g, c) Tbwd.insert ->
    (g, e) D.unoccurs ->
    (e, a, g, c) except_unoccurs_insert =
 fun e i unocc ->
  match i with
  | Now -> Except_unoccurs_insert (Now, Except_unoccurs (e, unocc))
  | Later i -> (
      match e with
      | Except_occurs (e, o) ->
          let (Except_unoccurs_insert (i, e)) = except_unoccurs_insert e i unocc in
          Except_unoccurs_insert (i, Except_occurs (e, o))
      | Except_unoccurs (e, u) ->
          let (Except_unoccurs_insert (i, e)) = except_unoccurs_insert e i unocc in
          Except_unoccurs_insert (Later i, Except_unoccurs (e, u)))

type (_, _, _) except_deg =
  | Except_deg : ('d, 'a) deg * ('e, 'd, 'c) except -> ('e, 'a, 'c) except_deg

let rec except_deg : type e a b c. e D.t -> (e, a, b) except -> (c, b) deg -> (e, a, c) except_deg =
 fun e ex s ->
  match (ex, s) with
  | Except_zero, Zero c ->
      let (Except ex) = except_dirs e c in
      Except_deg (Zero (excepted ex c), ex)
  | Except_occurs (ex, o), Suc (s, i) ->
      let (Except_deg (s, ex)) = except_deg e ex s in
      Except_deg (s, except_occurs_insert ex i o)
  | Except_unoccurs (ex, u), Suc (s, i) ->
      let (Except_deg (s, ex)) = except_deg e ex s in
      let (Except_unoccurs_insert (i, ex)) = except_unoccurs_insert ex i u in
      Except_deg (Suc (s, i), ex)

type (_, _, _) except_perm =
  | Except_perm : ('d, 'a) perm * ('e, 'd, 'c) except -> ('e, 'a, 'c) except_perm

let rec except_perm : type e a b c.
    e D.t -> (e, a, b) except -> (c, b) perm -> (e, a, c) except_perm =
 fun e ex s ->
  match (ex, s) with
  | Except_zero, Zero -> Except_perm (Zero, ex)
  | Except_occurs (ex, o), Suc (s, i) ->
      let (Except_perm (s, ex)) = except_perm e ex s in
      Except_perm (s, except_occurs_insert ex i o)
  | Except_unoccurs (ex, u), Suc (s, i) ->
      let (Except_perm (s, ex)) = except_perm e ex s in
      let (Except_unoccurs_insert (i, ex)) = except_unoccurs_insert ex i u in
      Except_perm (Suc (s, i), ex)

let rec deg_of_except : type e a b. b D.t -> (e, a, b) except -> (b, a) deg =
 fun b -> function
  | Except_zero -> deg_zero D.zero
  | Except_occurs (e, _) ->
      let (Word (Suc (b, Unit))) = b in
      deg_plus_dom (deg_of_except (Word b) e) (Suc (Zero, Unit))
  | Except_unoccurs (e, _) ->
      let (Word (Suc (b, Unit))) = b in
      Suc (deg_of_except (Word b) e, Now)
