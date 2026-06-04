open Util
open Tbwd

(* ********** Degeneracies ********** *)

(* Degeneracies are defined inductively by insertion: a degeneracy of 0 is given by adding any dimension, and a degeneracy of n+1 is one of length n together with a location at which to insert the n+1st (rightmost) element. *)

type (_, _) deg =
  | Zero : 'a D.t -> ('a, D.zero) deg
  | Suc : ('a, 'b) deg * 'g D.G.t * ('a, 'g, 'asuc) D.insert -> ('asuc, ('b, 'g) D.suc) deg

(* Another possible definition, "inductive on the other side", is:

   type (_, _) deg =
     | Zero : (D.zero, D.zero) deg
     | Deg : ('a, 'b) deg -> (('a, unit) D.suc, 'b) deg
     | Perm : ('a, 'b) deg * ('b, unit, 'bsuc) D.insert -> (('a, unit) D.suc, 'bsuc) deg
*)

let rec dom_deg : type m n. (m, n) deg -> m D.t = function
  | Zero a -> a
  | Suc (s, g, i) -> D.insert i (dom_deg s) g

let rec cod_deg : type m n. (m, n) deg -> n D.t = function
  | Zero _ -> D.zero
  | Suc (s, g, _) -> D.suc (cod_deg s) g

let rec id_deg : type n. n D.t -> (n, n) deg = function
  | Word Zero -> Zero D.zero
  | Word (Suc (n, g)) -> Suc (id_deg (Word n), g, Now)

(* By "residual" of a degeneracy, given an element of its codomain, we mean the image of that element together with the degeneracy obtained by removing that element from the codomain and its image from the domain. *)

type (_, _, _) deg_residual =
  | Residual :
      ('m, 'n) deg * 'g D.G.t * ('m, 'g, 'msuc) D.insert
      -> ('msuc, 'n, 'g) deg_residual

let rec deg_residual : type m n g npred.
    (m, n) deg -> (npred, g, n) D.insert -> (m, npred, g) deg_residual =
 fun s k ->
  match (k, s) with
  | Now, Suc (s, g, i) -> Residual (s, g, i)
  | Later k, Suc (s, g, i) ->
      let (Residual (s, g', j)) = deg_residual s k in
      let (Swap_inserts (i, j)) = D.swap_inserts i j in
      Residual (Suc (s, g, j), g', i)

(* Using residuals, we can compose degeneracies. *)
let rec comp_deg : type a b c. (b, c) deg -> (a, b) deg -> (a, c) deg =
 fun a b ->
  match a with
  | Zero _ -> Zero (dom_deg b)
  | Suc (s, _, k) ->
      let (Residual (t, g', i)) = deg_residual b k in
      Suc (comp_deg s t, g', i)

(* Dually, a "coresidual" of a degeneracy, given an element of its domain, is the coimage of that element, if any, together with the degeneracy obtained by removing that element from the domain and its coimage from the codomain. *)

type (_, _) deg_coresidual =
  | Coresidual_zero : ('m, 'n) deg -> ('m, 'n) deg_coresidual
  | Coresidual_suc :
      ('m, 'n) deg * 'g D.G.t * ('n, 'g, 'nsuc) D.insert
      -> ('m, 'nsuc) deg_coresidual

(* TODO: This function is currently single-generator only.  Generalizing to multi-generator requires a multi-generator [compare_inserts] in Word.ml that handles inserts with different middle generator types. *)
let rec deg_coresidual : type mpred m n.
    (m, n) deg -> (mpred, unit, m) D.insert -> (mpred, n) deg_coresidual =
 fun s k ->
  match s with
  | Zero m -> Coresidual_zero (Zero (D.uninsert k m))
  | Suc (s, g, j) -> (
      (* In single-generator code, j's middle generator is always unit; the assert is unreachable.  In a future multi-generator world, this needs proper handling of distinct generators. *)
      match D.G.compare g D.deg with
      | Neq -> assert false
      | Eq -> (
          match D.compare_inserts j k with
          | Eq_inserts -> Coresidual_suc (s, g, Now)
          | Neq_inserts (k', j') -> (
              match deg_coresidual s k' with
              | Coresidual_zero s' -> Coresidual_zero (Suc (s', g, j'))
              | Coresidual_suc (s', g'', i) -> Coresidual_suc (Suc (s', g, j'), g'', Later i))))

(* Extend a degeneracy by the identity on the right. *)
let rec deg_plus : type m n k mk nk.
    (m, n) deg -> (n, k, nk) D.plus -> (m, k, mk) D.plus -> (mk, nk) deg =
 fun s nk mk ->
  match (nk, mk) with
  | Zero, Zero -> s
  | Suc (nk, g), Suc (mk, _) -> Suc (deg_plus s nk mk, g, Now)

(* Extend the domain of a codegeneracy by a number of degenerate points, leaving the codomain fixed. *)
let rec deg_plus_dom : type m n k mk. (m, n) deg -> (m, k, mk) D.plus -> (mk, n) deg =
 fun s mk ->
  match s with
  | Zero m -> Zero (D.plus_out m mk)
  | Suc (s, g, i) ->
      let (Insert_plus (mk', j)) = D.insert_plus i mk in
      Suc (deg_plus_dom s mk', g, j)

(* Add together two degeneracies. *)
let rec deg_plus_deg : type m n mn k l kl.
    (k, m) deg -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) deg -> (kl, mn) deg =
 fun skm mn kl sln ->
  match (mn, sln) with
  | Zero, Zero _ -> deg_plus_dom skm kl
  | Suc (mn', _), Suc (sln', g, i) ->
      let (Plus kl') = D.plus (dom_deg sln') in
      Suc (deg_plus_deg skm mn' kl' sln', g, D.plus_insert kl' kl i)

(* Extend a degeneracy by the identity on the left. *)
let plus_deg : type m n mn l ml.
    m D.t -> (m, n, mn) D.plus -> (m, l, ml) D.plus -> (l, n) deg -> (ml, mn) deg =
 fun m mn ml s -> deg_plus_deg (id_deg m) mn ml s

(* The degeneracy (which is a permutation) that swaps two dimensions. *)
let rec swap_deg : type m n mn nm. (m, n, mn) D.plus -> (n, m, nm) D.plus -> (mn, nm) deg =
 fun mn nm ->
  match nm with
  | Zero ->
      let Eq = D.plus_uniq mn (D.zero_plus (D.plus_right mn)) in
      id_deg (D.plus_right mn)
  | Suc (nm', g) ->
      let (Insert_plus (mn', i)) = D.insert_plus Now mn in
      Suc (swap_deg mn' nm', g, i)

(* ********** Comparing degeneracies ********** *)

(* Check whether a degeneracy is an identity, identifying its domain and codomain if so. *)
let rec is_id_deg : type m n. (m, n) deg -> (m, n) Eq.t option = function
  | Zero n -> (
      match D.compare n D.zero with
      | Eq -> Some Eq
      | Neq -> None)
  | Suc (p, _, Now) -> (
      match is_id_deg p with
      | Some Eq -> Some Eq
      | None -> None)
  | Suc (_, _, Later _) -> None

(* A degeneracy of a positive dimension is still positive *)
let pos_deg : type m n. n D.pos -> (m, n) deg -> m D.pos =
 fun n s ->
  match (n, s) with
  | Pos _, Suc (s, g, i) -> D.insert_pos (dom_deg s) g i

(* Are two degeneracies exactly equal? *)
let deg_equal : type m n k l. (m, n) deg -> (k, l) deg -> unit option =
 fun s1 s2 ->
  match (D.compare (dom_deg s1) (dom_deg s2), D.compare (cod_deg s1) (cod_deg s2)) with
  | Eq, Eq ->
      (* Degeneracies with the same domain *and* codomain can be compared with simple structural equality. *)
      if s1 = s2 then Some () else None
  | _ -> None

(* Is one degeneracy, with greater codomain, an identity extension of another? *)
let rec deg_is_idext : type n l nl m k.
    (n, l, nl) D.plus -> (m, n) deg -> (k, nl) deg -> unit option =
 fun nl s1 s2 ->
  match (nl, s2) with
  | Zero, _ -> deg_equal s1 s2
  | Suc (nl, Unit), Suc (s2, _, Now) -> deg_is_idext nl s1 s2
  | _ -> None

(* We consider two degeneracies "equivalent" if they differ by an identity extension on the right (i.e. post-whiskering with an identity). *)
let deg_equiv : type m n k l. (m, n) deg -> (k, l) deg -> unit option =
 fun s1 s2 ->
  match D.trichotomy (cod_deg s1) (cod_deg s2) with
  | Eq -> deg_equal s1 s2
  | Lt nl -> deg_is_idext nl s1 s2
  | Gt nl -> deg_is_idext nl s2 s1

(* Every dimension is a degeneracy of zero. *)
let deg_zero : type a. a D.t -> (a, D.zero) deg = fun a -> Zero a

(* ********** Variable degeneracies ********** *)

type _ deg_of = Of : ('m, 'n) deg -> 'n deg_of
type _ deg_of_plus = Of : ('n, 'k, 'nk) D.plus * ('m, 'nk) deg -> 'n deg_of_plus

let comp_deg_of_plus : type m n. (m, n) deg -> m deg_of_plus -> n deg_of_plus =
 fun s2 (Of (mk, s1)) ->
  let (Plus nk) = D.plus (D.plus_right mk) in
  let s2k = deg_plus s2 nk mk in
  Of (nk, comp_deg s2k s1)

type (_, _) deg_extending =
  | DegExt : ('k, 'j, 'kj) D.plus * ('n, 'i, 'ni) D.plus * ('kj, 'ni) deg -> ('k, 'n) deg_extending

let comp_deg_extending : type m n l k. (m, n) deg -> (k, l) deg -> (k, n) deg_extending =
 fun a b ->
  (* let k = dom_deg b in *)
  let l = cod_deg b in
  let m = dom_deg a in
  (* let n = cod_deg a in *)
  let (Pushout (mi, lj)) = D.pushout m l in
  let (Plus kj) = D.plus (Word lj) in
  let (Plus ni) = D.plus (Word mi) in
  DegExt (kj, ni, comp_deg (deg_plus a ni mi) (deg_plus b lj kj))

type any_deg = Any_deg : ('m, 'n) deg -> any_deg

(* ******************** Printing and parsing ******************** *)

(* A degeneracy is represented by a list of positive integers and strings.  The integers give a permutation of the codomain, and the strings are endpoint-denoting characters indicating where degeneracies are inserted in the domain.  Thus the length of the list is equal to the length of the domain. *)

let rec strings_of_deg : type a b. int -> (a, b) deg -> string list =
 fun i -> function
  | Zero a -> List.init (D.length a) (fun _ -> Endpoints.refl_string ())
  | Suc (s, _, k) ->
      List_extra.insert (Tbwd.int_of_insert k) (string_of_int i) (strings_of_deg (i + 1) s)

let string_of_deg : type a b. (a, b) deg -> string =
 fun s -> String.concat (if D.length (cod_deg s) > 9 then "-" else "") (strings_of_deg 1 s)

type _ deg_to = To : ('m, 'n) deg -> 'm deg_to

(* The Bwv is the list of strings, and n is the dimension of its domain.  Their lengths must agree (both are the length of the input list); the caller is responsible for that.  We could parametrize the Bwv by the dimension, but Bwv is parametrized by N, not D, and after the wordunit refactor those are no longer the same type.  *)
let rec deg_of_strings : type n a.
    n D.t -> ([ `Int of int | `Str of string ], a) Bwv.t -> int -> n deg_to option =
 fun n xs i ->
  let open Monad.Ops (Monad.Maybe) in
  let finished () =
    if Bwv.fold_right (fun x b -> x = `Str (Endpoints.refl_string ()) && b) xs true then
      Some (To (Zero n))
    else None in
  (* We find where the expected number of the *codomain* occurs and remove it, remembering its index to supply to Suc.
     If the list is empty, or if we otherwise don't find it, then we must have removed all the numbers and only refl strings are left. *)
  match xs with
  | Emp -> finished ()
  | Snoc _ -> (
      match Bwv.find_remove (`Int i) xs with
      | None -> finished ()
      | Some (xs, j) -> (
          (* IF we do find it, then what's left we can recurse into with an incremented expectation. *)
          match n with
          | Word Zero -> None
          | Word (Suc (n_pred, _)) ->
              let* (Into (g, j_idx)) = D.insert_of_int n (N.int_of_index j) in
              let* (To s) = deg_of_strings (Word n_pred) xs (i + 1) in
              (* TODO: bridge existentials via Word.compare; in a future multi-generator world this should be expressed without this comparison. *)
              match D.compare (D.uninsert j_idx n) (dom_deg s) with
              | Eq -> return (To (Suc (s, g, j_idx)))
              | Neq -> None))

(* We could write the next function monadically to include the errors as options, but it's simpler to just raise a local exception. *)
exception Invalid_direction_name of string

(* A list of positive integers and strings is represented by a single string that either concatenates them, if the integers are all <10 and the strings are all 1-character, or concatenates them with '-' between otherwise.  There is no confusion because if a degeneracy consists of a single number, that number can only be 1, so a multi-digit string must be concatenated.  *)
let deg_of_string : string -> any_deg option =
 fun str ->
  (* First we break our string into a list, as in the input to deg_of_strings, and simultaneously compute its maximum. *)
  let strs =
    if String.contains str '-' then String.split_on_char '-' str
    else String.fold_right (fun c s -> String.make 1 c :: s) str [] in
  let parsestr x m =
    match int_of_string_opt x with
    | Some i -> (`Int i, max i m)
    | None -> if x = Endpoints.refl_string () then (`Str x, m) else raise (Invalid_direction_name x)
  in
  try
    let Wrap strs, _i =
      List.fold_right
        (fun c (Bwv.Wrap l, i) ->
          let x, i = parsestr c i in
          (Wrap (Snoc (l, x)), i))
        strs (Wrap Emp, 0) in
    (* Build a D.t whose int length matches the Bwv strs.  deg_of_strings trusts these to agree at runtime. *)
    let (D.Wrap n) = D.of_int (N.to_int (Bwv.length strs)) in
    (* Finally we pass off to deg_of_strings. *)
    match deg_of_strings n strs 1 with
    | None -> None
    | Some (To s) -> Some (Any_deg s)
  with Invalid_direction_name _ -> None

(* A degeneracy is "locking" if it has degenerate external directions. *)
let rec locking : type a b. (a, b) deg -> bool = function
  | Suc (s, _, _) -> locking s
  | Zero x -> (
      match D.compare x D.zero with
      | Eq -> false
      | Neq -> true && not (Endpoints.internal ()))
