open Util
open Dim

(* An element of "mn variables" is an mn-dimensional cube of variables where mn = m + n and the user specified names for n dimensions, with the other m dimensions being named with face suffixes.  The generic version "gvariables" allows any type of "names". *)

type (_, _) gvariables =
  | Variables :
      'm D.t * ('m, 'n, 'mn) D.plus * (N.zero, 'n, 'a, 'f) NICubeOf.t
      -> ('mn, 'a) gvariables

type 'mn variables = ('mn, string option) gvariables
type any_variables = Any : 'n variables -> any_variables

let top_variable : type m a. (m, a) gvariables -> a = function
  | Variables (_, _, xs) -> NICubeOf.find_top xs

let find_variable : type m n a. (m, n) sface -> (n, a) gvariables -> a =
 fun s (Variables (_m, mn, xs)) ->
  let (SFace_of_plus (_, _, sn)) = sface_of_plus mn s in
  NICubeOf.find xs sn

let sub_variables : type kl mn a. (kl, mn) sface -> (mn, a) gvariables -> (kl, a) gvariables =
 fun s (Variables (_m, mn, xs)) ->
  let (SFace_of_plus (kl, sm, sn)) = sface_of_plus mn s in
  let module T = NICubeOf.Traverse (struct
    type 'a t = unit
  end) in
  let (Wrap (xs, ())) =
    T.build_left (dom_sface sn)
      { build = (fun fb () -> Fwrap (NFamOf (NICubeOf.find xs (comp_sface sn fb)), ())) }
      () in
  Variables (dom_sface sm, kl, xs)

let plus_variables : type k mn kmn a.
    k D.t -> (k, mn, kmn) D.plus -> (mn, a) gvariables -> (kmn, a) gvariables =
 fun k k_mn (Variables (m, m_n, xs)) ->
  let (Plus k_m) = D.plus m in
  let km_n = D.plus_assocl k_m m_n k_mn in
  Variables (D.plus_out k k_m, km_n, xs)

let dim_variables : type m a. (m, a) gvariables -> m D.t = function
  | Variables (m, mn, _) -> D.plus_out m mn

let singleton_variables : type m a. m D.t -> a -> (m, a) gvariables =
 fun m x -> Variables (m, D.plus_zero m, NICubeOf.singleton x)
