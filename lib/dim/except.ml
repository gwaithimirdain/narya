open Util
open Tbwd
open Sface
open Tface
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

(* We can transfer faces, degeneracies and permutations "downwards" along an except. *)

type (_, _, _) except_sface =
  | Except_sface : ('d, 'a) sface * ('e, 'd, 'c) except -> ('e, 'a, 'c) except_sface

let rec except_sface : type e a b c. (e, a, b) except -> (c, b) sface -> (e, a, c) except_sface =
 fun e s ->
  match (e, s) with
  | Except_zero, Zero -> Except_sface (Zero, Except_zero)
  | Except_occurs (e, _), End (s, _, _) -> except_sface e s
  | Except_occurs (e, o), Mid (s, _) ->
      let (Except_sface (s, e)) = except_sface e s in
      Except_sface (s, Except_occurs (e, o))
  | Except_unoccurs (e, _), End (s, g, l) ->
      let (Except_sface (s, e)) = except_sface e s in
      Except_sface (End (s, g, l), e)
  | Except_unoccurs (e, u), Mid (s, g) ->
      let (Except_sface (s, e)) = except_sface e s in
      Except_sface (Mid (s, g), Except_unoccurs (e, u))

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
  | Except_occurs (ex, o), Suc (s, _, i) ->
      let (Except_deg (s, ex)) = except_deg e ex s in
      Except_deg (s, except_occurs_insert ex i o)
  | Except_unoccurs (ex, u), Suc (s, g, i) ->
      let (Except_deg (s, ex)) = except_deg e ex s in
      let (Except_unoccurs_insert (i, ex)) = except_unoccurs_insert ex i u in
      Except_deg (Suc (s, g, i), ex)

type (_, _, _) except_perm =
  | Except_perm : ('d, 'a) perm * ('e, 'd, 'c) except -> ('e, 'a, 'c) except_perm

let rec except_perm : type e a b c.
    e D.t -> (e, a, b) except -> (c, b) perm -> (e, a, c) except_perm =
 fun e ex s ->
  match (ex, s) with
  | Except_zero, Zero -> Except_perm (Zero, ex)
  | Except_occurs (ex, o), Suc (s, _, i) ->
      let (Except_perm (s, ex)) = except_perm e ex s in
      Except_perm (s, except_occurs_insert ex i o)
  | Except_unoccurs (ex, u), Suc (s, g, i) ->
      let (Except_perm (s, ex)) = except_perm e ex s in
      let (Except_unoccurs_insert (i, ex)) = except_unoccurs_insert ex i u in
      Except_perm (Suc (s, g, i), ex)

(* We can also transfer faces, though not degeneracies, "upwards". *)

type (_, _, _) sface_except =
  | Sface_except : ('e, 'c, 'd) except * ('d, 'b) sface -> ('e, 'b, 'c) sface_except

let rec sface_except : type e a b c.
    b D.t -> (c, a) sface -> (e, a, b) except -> (e, b, c) sface_except =
 fun b s e ->
  match (b, e) with
  | Word Zero, Except_zero ->
      let Zero = s in
      Sface_except (Except_zero, Zero)
  | Word (Suc (b, Unit)), Except_occurs (e, o) ->
      let (Sface_except (e, s)) = sface_except (Word b) s e in
      Sface_except (Except_occurs (e, o), Mid (s, D.deg))
  | Word (Suc (b, Unit)), Except_unoccurs (e, u) -> (
      match s with
      | End (s, g, p) ->
          let (Sface_except (e, s)) = sface_except (Word b) s e in
          Sface_except (e, End (s, g, p))
      | Mid (s, g) ->
          let (Sface_except (e, s)) = sface_except (Word b) s e in
          Sface_except (Except_unoccurs (e, u), Mid (s, g)))

type (_, _, _) pface_except =
  | Pface_except : ('e, 'c, 'd) except * ('d, 'b) pface -> ('e, 'b, 'c) pface_except

let rec pface_except : type e a b c.
    b D.t -> (c, a) pface -> (e, a, b) except -> (e, b, c) pface_except =
 fun b s e ->
  match (b, e) with
  | Word Zero, Except_zero -> (
      match s with
      | _ -> .)
  | Word (Suc (b, Unit)), Except_occurs (e, o) ->
      let (Pface_except (e, s)) = pface_except (Word b) s e in
      Pface_except (Except_occurs (e, o), Mid (s, D.deg))
  | Word (Suc (b, Unit)), Except_unoccurs (e, u) -> (
      match s with
      | End (s, _, g, p) ->
          let (Sface_except (e, s)) = sface_except (Word b) s e in
          Pface_except (e, End (s, D.zero_plus (cod_sface s), g, p))
      | Mid (s, g) ->
          let (Pface_except (e, s)) = pface_except (Word b) s e in
          Pface_except (Except_unoccurs (e, u), Mid (s, g)))

(* But every except does give rise to a degeneracy that adds in the excepted directions.  *)

let rec deg_of_except : type e a b. b D.t -> (e, a, b) except -> (b, a) deg =
 fun b -> function
  | Except_zero -> deg_zero D.zero
  | Except_occurs (e, _) ->
      let (Word (Suc (b, Unit))) = b in
      deg_plus_dom (deg_of_except (Word b) e) (Suc (Zero, Unit))
  | Except_unoccurs (e, _) ->
      let (Word (Suc (b, Unit))) = b in
      Suc (deg_of_except (Word b) e, D.deg, Now)

(* In the unary case, the degeneracy deg_of_except has a section given by choosing the unique endpoint for each omitted direction.  This is convenient when formulating algorithms for pushing filtered dimensions through environments.  We therefore generalize it to other arities by using an "optional sface", trusting that the missing endpoints will be canceled out by a degeneracy at the other end.  Consistent mode/dimension theories will ensure this.  In particular, in the non-unary case there should not be any modal 2-cells from a less-nonparametric modality to a more non-parametric one.  *)
let sface_of_except : type e a b. b D.t -> (e, a, b) except -> (a, b) opt_sface =
 fun b ex ->
  let rec go : type l e a b. l Endpoints.t option -> b D.t -> (e, a, b) except -> (a, b) opt_sface =
   fun endpt b ex ->
    match (ex, b) with
    | Except_zero, _ -> Zero
    | Except_occurs (ex, _), Word (Suc (b, Unit)) -> End (go endpt (Word b) ex, D.deg, endpt)
    | Except_unoccurs (ex, _), Word (Suc (b, Unit)) -> Mid (go endpt (Word b) ex, D.deg) in
  match Endpoints.unary () with
  | Some e -> go (Some (e, Top)) b ex
  | None -> go None b ex

let rec except_comp : type e1 e2 e12 a b c.
    (e1, e2, e12) D.plus -> (e2, a, b) except -> (e1, b, c) except -> (e12, a, c) except =
 fun e12 ex2 ex1 ->
  match ex1 with
  | Except_zero ->
      let Except_zero = ex2 in
      Except_zero
  | Except_occurs (ex1, o) -> Except_occurs (except_comp e12 ex2 ex1, D.occurs_plus_left e12 o)
  | Except_unoccurs (ex1, u1) -> (
      match ex2 with
      | Except_occurs (ex2, o2) ->
          Except_occurs (except_comp e12 ex2 ex1, D.occurs_plus_right e12 o2)
      | Except_unoccurs (ex2, u2) ->
          Except_unoccurs (except_comp e12 ex2 ex1, D.unoccurs_plus e12 u1 u2))

let rec except_comp' : type e1 e2 e12 a b c.
    (e1, e2, e12) D.plus -> (e2, b, c) except -> (e1, a, b) except -> (e12, a, c) except =
 fun e12 ex2 ex1 ->
  match ex2 with
  | Except_zero ->
      let Except_zero = ex1 in
      Except_zero
  | Except_occurs (ex2, o) -> Except_occurs (except_comp' e12 ex2 ex1, D.occurs_plus_right e12 o)
  | Except_unoccurs (ex2, u2) -> (
      match ex1 with
      | Except_occurs (ex1, o1) ->
          Except_occurs (except_comp' e12 ex2 ex1, D.occurs_plus_left e12 o1)
      | Except_unoccurs (ex1, u1) ->
          Except_unoccurs (except_comp' e12 ex2 ex1, D.unoccurs_plus e12 u1 u2))
