open Util

(* Add the same dimension on the left of everything in a tbwd of dimensions. *)

module Anyplus = struct
  module Param = D
  module Dom = D
  module Cod = D

  type ('p, 'a, 'b) t = ('p, 'a, 'b) D.plus

  let cod : type p a b. p Param.t -> (p, a, b) t -> b Cod.t = fun p pa -> D.plus_out p pa
  let dom : type p a b. p Param.t -> (p, a, b) t -> a Dom.t = fun _ pa -> D.plus_right pa

  type (_, _) exists = Exists : ('p, 'a, 'b) t -> ('p, 'a) exists

  let exists : type p a. p Param.t -> a Dom.t -> (p, a) exists =
   fun _ a ->
    let (Plus ab) = D.plus a in
    Exists ab

  let uniq : type p a b1 b2. (p, a, b1) t -> (p, a, b2) t -> (b1, b2) Eq.t = D.plus_uniq
end

include Word.Fmap (D) (D) (Anyplus)

(* We redefine these so they have the full interface. *)
module Dom = Word.Make (D)
module Cod = Word.Make (D)

let rec assocl : type a b ab cs bcs abcs.
    (a, b, ab) D.plus -> (b, cs, bcs) t -> (a, bcs, abcs) t -> (ab, cs, abcs) t =
 fun ab bcs abcs ->
  match (bcs, abcs) with
  | Zero, Zero -> Zero
  | Suc (bcs, Inject bc, Suc (Zero, _)), Suc (abcs, Inject a_bc, Suc (Zero, y)) ->
      let ab_c = D.plus_assocl ab bc a_bc in
      Suc (assocl ab bcs abcs, Inject ab_c, Suc (Zero, y))

let rec zerol : type bs. bs Dom.t -> (D.zero, bs, bs) t = function
  | Word Zero -> Zero
  | Word (Suc (bs, b)) -> Suc (zerol (Word bs), Inject (D.zero_plus b), Suc (Zero, b))
