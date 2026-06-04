open Util
open Tbwd
open Sface
open Deg

(* ********** Omitting directions ********** *)

(* ('e, 'a, 'b) except means that 'a is obtained from 'b by omitting all occurrences of any directions appearing in 'e. *)

type (_, _, _) except =
  | Except_zero : ('e, D.zero, D.zero) except
  | Except_occurs : ('e, 'a, 'b) except * ('g, 'e) D.occurs -> ('e, 'a, ('b, 'g) snoc) except
  | Except_unoccurs :
      ('e, 'a, 'b) except * ('g, 'e) D.unoccurs
      -> ('e, ('a, 'g) snoc, ('b, 'g) snoc) except

type (_, _) has_except = Except : ('e, 'a, 'b) except -> ('e, 'b) has_except

let rec except_dirs : type e b. e D.t -> b D.t -> (e, b) has_except =
 fun e -> function
  | Word Zero -> Except Except_zero
  | Word (Suc (b, h)) -> (
      let (Except ex) = except_dirs e (Word b) in
      match D.occurs h e with
      | Left o -> Except (Except_occurs (ex, o))
      | Right u -> Except (Except_unoccurs (ex, u)))

let except_zero : ('e, D.zero, D.zero) except = Except_zero

let rec excepted : type e a b. (e, a, b) except -> b D.t -> a D.t =
 fun ex b ->
  match (ex, b) with
  | Except_zero, Word Zero -> Word Zero
  | Except_occurs (ex, _), Word (Suc (b, _)) -> excepted ex (Word b)
  | Except_unoccurs (ex, _), Word (Suc (b, g)) ->
      let (Word a) = excepted ex (Word b) in
      Word (Suc (a, g))

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
