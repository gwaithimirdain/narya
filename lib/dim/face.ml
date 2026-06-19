open Perm
open Sface

(* A face is a permutation followed by a strict face, hence a map as for a strict face that need not be order-preserving. *)

type (_, _) face = Face : ('m, 'n) sface * ('k, 'm) perm -> ('k, 'n) face

let id_face : type n. n D.t -> (n, n) face = fun n -> Face (id_sface n, id_perm n)

(* Faces are closed under composition, by way of a distributive law between permutations and strict faces. *)

let rec perm_sface : type m n k. (n, k) perm -> (m, n) sface -> (m, k) face =
 fun a b ->
  match a with
  | Zero -> Face (b, id_perm (dom_sface b))
  | Suc (p, k) -> (
      match sface_residual b k with
      | Residual_End (f, e) ->
          let (Face (f', p')) = perm_sface p f in
          Face (End (f', e), p')
      | Residual_Mid (f, l) ->
          let (Face (f', p')) = perm_sface p f in
          Face (Mid f', Suc (p', l)))

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
