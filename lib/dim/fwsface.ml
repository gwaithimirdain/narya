open Util
open Tlist
open Sface

type (_, _) fwsface =
  | Zero : (nil, nil) fwsface
  | End : 'g D.G.t * 'l Endpoints.t * ('m, 'n) fwsface -> ('m, ('g, 'n) cons) fwsface
  | Mid : 'g D.G.t * ('m, 'n) fwsface -> (('g, 'm) cons, ('g, 'n) cons) fwsface

(* The domain and codomain of a forwards face, as forwards words. *)

let rec dom_fwsface : type m n. (m, n) fwsface -> m D.fwd = function
  | Zero -> Nil
  | End (_, _, f) -> dom_fwsface f
  | Mid (g, f) -> Cons (g, dom_fwsface f)

let rec cod_fwsface : type m n. (m, n) fwsface -> n D.fwd = function
  | Zero -> Nil
  | End (g, _, f) -> Cons (g, cod_fwsface f)
  | Mid (g, f) -> Cons (g, cod_fwsface f)

let rec sface_plus_fw : type a c ac b d bd.
    (a, c, ac) D.bplus -> (b, d, bd) D.bplus -> (a, b) sface -> (c, d) fwsface -> (ac, bd) sface =
 fun ac bd f1 f2 ->
  match f2 with
  | Zero ->
      let Append_nil, Append_nil = (ac, bd) in
      f1
  | End (g, e, f2) ->
      let (Append_cons bd) = bd in
      sface_plus_fw ac bd (End (f1, g, e)) f2
  | Mid (g, f2) ->
      let Append_cons ac, Append_cons bd = (ac, bd) in
      sface_plus_fw ac bd (Mid (f1, g)) f2

let sface_of_fw : type c ac d bd.
    (D.zero, c, ac) D.bplus -> (D.zero, d, bd) D.bplus -> (c, d) fwsface -> (ac, bd) sface =
 fun ac bd f -> sface_plus_fw ac bd Zero f
