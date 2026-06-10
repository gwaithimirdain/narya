open Perm
open Sface

(* A face is a permutation followed by a strict face, hence a map as for a strict face that need not be order-preserving. *)

type (_, _) face = Face : ('m, 'n) sface * ('k, 'm) perm -> ('k, 'n) face

let id_face : type n. n D.t -> (n, n) face = fun n -> Face (id_sface n, id_perm n)

(* Faces are closed under composition, by way of a distributive law between permutations and strict faces.  To define this we need a similar sort of "residual" of a strict face and an index, which picks out the image of that index and the strict face with that index and its image (if any) removed. *)

(* The residual is indexed by the generator of the extracted element, so that callers can see at the type level that it matches the generator they removed from the codomain. *)
type (_, _, _) sface_residual =
  | End : ('m, 'n) sface * 'l Endpoints.t -> ('m, 'g, 'n) sface_residual
  | Mid : ('m, 'n) sface * ('m, 'g, 'msuc) D.insert -> ('msuc, 'g, 'n) sface_residual

let rec sface_residual : type m n g npred.
    (m, n) sface -> (npred, g, n) D.insert -> (m, g, npred) sface_residual =
 fun f k ->
  match (k, f) with
  | Now, End (f', _, e) -> End (f', e)
  | Now, Mid (f', _) -> Mid (f', Now)
  | Later k', End (f', g, e) -> (
      match sface_residual f' k' with
      | End (f'', e') -> End (End (f'', g, e), e')
      | Mid (f'', l) -> Mid (End (f'', g, e), l))
  | Later k', Mid (f', g) -> (
      match sface_residual f' k' with
      | End (f'', e') -> End (Mid (f'', g), e')
      | Mid (f'', l) -> Mid (Mid (f'', g), Later l))

let rec perm_sface : type m n k. (n, k) perm -> (m, n) sface -> (m, k) face =
 fun a b ->
  match a with
  | Zero -> Face (b, id_perm (dom_sface b))
  | Suc (p, g_perm, k) -> (
      match sface_residual b k with
      | End (f, e) ->
          let (Face (f', p')) = perm_sface p f in
          Face (End (f', g_perm, e), p')
      | Mid (f, l) ->
          let (Face (f', p')) = perm_sface p f in
          Face (Mid (f', g_perm), Suc (p', g_perm, l)))

let comp_face : type m n k. (n, k) face -> (m, n) face -> (m, k) face =
 fun (Face (a, b)) (Face (c, d)) ->
  let (Face (c', b')) = perm_sface b c in
  Face (comp_sface a c', comp_perm b' d)

let dom_face : type m n. (m, n) face -> m D.t = function
  | Face (_, p) -> dom_perm p

let cod_face : type m n. (m, n) face -> n D.t = function
  | Face (f, _) -> cod_sface f

let face_of_sface : type m n. (m, n) sface -> (m, n) face = fun f -> Face (f, id_perm (dom_sface f))
let face_of_perm : type m n. (m, n) perm -> (m, n) face = fun p -> Face (id_sface (cod_perm p), p)

type _ face_of = Face_of : ('m, 'n) face -> 'n face_of
