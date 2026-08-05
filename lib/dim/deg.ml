open Util
open Sdeg
open Perm

(* ********** Degeneracies ********** *)

(* Just as a face is a permutation followed by a strict face, a degeneracy is a strict degeneracy (see Sdeg) followed by a permutation.  This factorization is unique: the strict degeneracy records which generators of the domain survive, in order, while the permutation records the order in which they appear in the codomain.  Thus, as for faces, degeneracies can be compared by structural equality, and composed by a distributive law. *)

type (_, _) deg = Deg : ('m, 'k) sdeg * ('k, 'n) perm -> ('m, 'n) deg

let dom_deg : type m n. (m, n) deg -> m D.t = fun (Deg (s, _)) -> dom_sdeg s
let cod_deg : type m n. (m, n) deg -> n D.t = fun (Deg (_, p)) -> cod_perm p
let id_deg : type n. n D.t -> (n, n) deg = fun n -> Deg (id_sdeg n, id_perm n)

(* Every dimension is a degeneracy of zero. *)
let deg_zero : type a. a D.t -> (a, D.zero) deg = fun a -> Deg (sdeg_zero a, Zero)

(* Every permutation is a degeneracy, with no strict part. *)
let deg_of_perm : type m n. (m, n) perm -> (m, n) deg = fun p -> Deg (id_sdeg (dom_perm p), p)

(* Conversely, a degeneracy is a permutation exactly when its strict part is an identity. *)
let perm_of_deg : type m n. (m, n) deg -> (m, n) perm option =
 fun (Deg (s, p)) ->
  match is_id_sdeg s with
  | Some Eq -> Some p
  | None -> None

(* A degeneracy with zero domain also has zero codomain. *)
let deg_zero_dom : type n. (D.zero, n) deg -> (D.zero, n) Eq.t =
 fun (Deg (s, p)) ->
  let Zero = s in
  let Zero = p in
  Eq

(* Add to the codomain a new outermost generator, whose preimage is inserted at a specified place in the domain.  This was the Suc constructor of the older, unfactored, definition of degeneracies: the new generator survives, and it is outermost in the codomain, so the permutation grows by a Suc. *)
let deg_suc : type a b g asuc.
    (a, b) deg -> g D.G.t -> (a, g, asuc) D.insert -> (asuc, (b, g) D.suc) deg =
 fun (Deg (s, p)) g i ->
  let (Sdeg_insert (s, j)) = sdeg_insert s g i in
  Deg (s, Suc (p, g, j))

(* By "residual" of a degeneracy, given an element of its codomain, we mean the image of that element together with the degeneracy obtained by removing that element from the codomain and its image from the domain.  This inverts deg_suc. *)
type (_, _, _) deg_residual =
  | Residual : ('m, 'n) deg * 'g D.G.t * ('m, 'g, 'msuc) D.insert -> ('msuc, 'n, 'g) deg_residual

let deg_residual : type m n g npred.
    (m, n) deg -> (npred, g, n) D.insert -> (m, npred, g) deg_residual =
 fun (Deg (s, p)) k ->
  let (D.Residual (p, g, i)) = D.perm_residual p k in
  let (Sdeg_uninsert (s, j)) = sdeg_uninsert s i in
  Residual (Deg (s, p), g, j)

(* Dually, a "coresidual" of a degeneracy, given an element of its domain, is the coimage of that element, if any, together with the degeneracy obtained by removing that element from the domain and its coimage from the codomain.  The element has a coimage exactly when the strict part doesn't degenerate it. *)

(* The coresidual is indexed by the generator of the removed element, so that callers can see at the type level that the coimage has the same generator. *)
type (_, _, _) deg_coresidual =
  | Coresidual_zero : ('m, 'n) deg -> ('m, 'g, 'n) deg_coresidual
  | Coresidual_suc : ('m, 'n) deg * ('n, 'g, 'nsuc) D.insert -> ('m, 'g, 'nsuc) deg_coresidual

let deg_coresidual : type mpred g m n.
    (m, n) deg -> (mpred, g, m) D.insert -> (mpred, g, n) deg_coresidual =
 fun (Deg (s, p)) k ->
  match sdeg_coresidual s k with
  | Coresidual_degen s -> Coresidual_zero (Deg (s, p))
  | Coresidual_keep (s, i) ->
      let (D.Coresidual (p, j)) = D.perm_coresidual p i in
      Coresidual_suc (Deg (s, p), j)

(* ********** Composition ********** *)

(* The distributive law: a permutation followed by a strict degeneracy is a strict degeneracy followed by a permutation.  The strict degeneracy peels the outermost generator of its domain, which the permutation's residual locates in *its* domain; the generator then survives or not in the new strict degeneracy according as it did in the old one. *)
let rec perm_sdeg : type a b c. (a, b) perm -> (b, c) sdeg -> (a, c) deg =
 fun p s ->
  match s with
  | Zero ->
      let Zero = p in
      Deg (Zero, Zero)
  | Suc (s, _) ->
      let (D.Residual (p, g, i)) = D.perm_residual p Now in
      let (Deg (t, q)) = perm_sdeg p s in
      let (Sdeg_insert (t, j)) = sdeg_insert t g i in
      Deg (t, Suc (q, g, j))
  | Degen (s, _) ->
      let (D.Residual (p, g, i)) = D.perm_residual p Now in
      let (Deg (t, q)) = perm_sdeg p s in
      Deg (sdeg_insert_degen t g i, q)

(* Hence degeneracies compose, exactly as faces do. *)
let comp_deg : type a b c. (b, c) deg -> (a, b) deg -> (a, c) deg =
 fun (Deg (a, b)) (Deg (c, d)) ->
  let (Deg (c', b')) = perm_sdeg d a in
  Deg (comp_sdeg c' c, comp_perm b b')

(* ********** Sums ********** *)

(* Extend a degeneracy by the identity on the right. *)
let deg_plus : type m n k mk nk.
    (m, n) deg -> (n, k, nk) D.plus -> (m, k, mk) D.plus -> (mk, nk) deg =
 fun (Deg (s, p)) nk mk ->
  let (Plus jk) = D.plus (D.plus_right nk) in
  Deg (sdeg_plus s jk mk, perm_plus p nk jk)

(* Extend the domain of a codegeneracy by a number of degenerate points, leaving the codomain fixed. *)
let deg_plus_dom : type m n k mk. (m, n) deg -> (m, k, mk) D.plus -> (mk, n) deg =
 fun (Deg (s, p)) mk -> Deg (sdeg_plus_dom s mk, p)

(* Add together two degeneracies. *)
let deg_plus_deg : type m n mn k l kl.
    (k, m) deg -> (m, n, mn) D.plus -> (k, l, kl) D.plus -> (l, n) deg -> (kl, mn) deg =
 fun (Deg (s1, p1)) mn kl (Deg (s2, p2)) ->
  let (Plus jj) = D.plus (dom_perm p2) in
  Deg (sdeg_plus_sdeg s1 jj kl s2, perm_plus_perm p1 mn jj p2)

(* Extend a degeneracy by the identity on the left. *)
let plus_deg : type m n mn l ml.
    m D.t -> (m, n, mn) D.plus -> (m, l, ml) D.plus -> (l, n) deg -> (ml, mn) deg =
 fun m mn ml s -> deg_plus_deg (id_deg m) mn ml s

(* The degeneracy (which is a permutation) that swaps two dimensions. *)
let swap_deg : type m n mn nm. (m, n, mn) D.plus -> (n, m, nm) D.plus -> (mn, nm) deg =
 fun mn nm -> deg_of_perm (perm_swap mn nm)

(* A degeneracy with codomain a sum of dimensions might decompose as a sum of a degeneracy and a permutation. *)
type (_, _, _) deg_perm_of_plus =
  | Deg_perm_of_plus :
      ('m, 'l, 'ml) D.plus * ('m, 'n) deg * ('l, 'k) perm
      -> ('ml, 'n, 'k) deg_perm_of_plus
  | None_deg_perm_of_plus : ('mk, 'n, 'k) deg_perm_of_plus

let rec deg_perm_of_plus : type ml n k nk.
    (n, k, nk) D.plus -> (ml, nk) deg -> (ml, n, k) deg_perm_of_plus =
 fun nk s ->
  match nk with
  | Zero -> Deg_perm_of_plus (Zero, s, id_perm D.zero)
  | Suc (nk, _) -> (
      let (Residual (s, g, i)) = deg_residual s Now in
      match deg_perm_of_plus nk s with
      | None_deg_perm_of_plus -> None_deg_perm_of_plus
      | Deg_perm_of_plus (mk, s, p) -> (
          match D.insert_into_plus g mk i with
          | Left _ -> None_deg_perm_of_plus
          | Right (j, mk') -> Deg_perm_of_plus (mk', s, Suc (p, g, j))))

(* ********** Comparing degeneracies ********** *)

(* Check whether a degeneracy is an identity, identifying its domain and codomain if so. *)
let is_id_deg : type m n. (m, n) deg -> (m, n) Eq.t option =
 fun (Deg (s, p)) ->
  match (is_id_sdeg s, is_id_perm p) with
  | Some Eq, Eq -> Some Eq
  | _ -> None

(* A degeneracy of a positive dimension is still positive *)
let pos_deg : type m n. n D.pos -> (m, n) deg -> m D.pos =
 fun n (Deg (s, p)) -> sdeg_pos (perm_pos n p) s

(* Are two degeneracies exactly equal? *)
let deg_equal : type m n k l. (m, n) deg -> (k, l) deg -> unit option =
 fun s1 s2 ->
  match (D.compare (dom_deg s1) (dom_deg s2), D.compare (cod_deg s1) (cod_deg s2)) with
  | Eq, Eq ->
      (* Degeneracies with the same domain *and* codomain can be compared with simple structural equality. *)
      if s1 = s2 then Some () else None
  | _ -> None

(* Is one degeneracy, with greater codomain, an identity extension of another? *)
let deg_is_idext : type n l nl m k. (n, l, nl) D.plus -> (m, n) deg -> (k, nl) deg -> unit option =
 fun nl s1 s2 ->
  let (Plus ml) = D.plus (D.plus_right nl) in
  deg_equal (deg_plus s1 nl ml) s2

(* We consider two degeneracies "equivalent" if they differ by an identity extension on the right (i.e. post-whiskering with an identity). *)
let deg_equiv : type m n k l. (m, n) deg -> (k, l) deg -> unit option =
 fun s1 s2 ->
  match D.trichotomy (cod_deg s1) (cod_deg s2) with
  | Eq -> deg_equal s1 s2
  | Lt nl -> deg_is_idext nl s1 s2
  | Gt nl -> deg_is_idext nl s2 s1
  | Incomparable -> None

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
 fun i s ->
  match D.compare_zero (cod_deg s) with
  | Zero -> List.init (D.length (dom_deg s)) (fun _ -> Endpoints.refl_string ())
  | Pos (Pos _) ->
      let (Residual (s, _, k)) = deg_residual s Now in
      List_extra.insert (D.int_of_insert k) (string_of_int i) (strings_of_deg (i + 1) s)

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
      Some (To (deg_zero n))
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
          | Word (Suc (n_pred, _)) -> (
              let* (Into (g, j_idx)) = D.insert_of_int n (N.int_of_index j) in
              let* (To s) = deg_of_strings (Word n_pred) xs (i + 1) in
              (* Parsing user input requires a runtime check that the recursively-parsed degeneracy has the expected domain. *)
              match D.compare (D.uninsert j_idx n) (dom_deg s) with
              | Eq -> return (To (deg_suc s g j_idx))
              | Neq -> None)))

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
let locking : type a b. (a, b) deg -> bool =
 fun (Deg (s, _)) -> sdeg_is_degenerating s && not (Endpoints.internal ())

(* The word of dimensions degenerated by a degeneracy: those inserted into its domain that are not images of the codomain, i.e. the word at its base.  This is functorial: the degenerated word of a composite is the concatenation (up to permutation) of the degenerated words of the factors, and permutations degenerate nothing. *)
let degenerated_dims : type a b. (a, b) deg -> D.wrapped = fun (Deg (s, _)) -> sdeg_degenerated s
