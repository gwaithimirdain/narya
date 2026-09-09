type one = D.one

(* A word is a singleton if it consists of exactly one generator, of any kind. *)
type _ is_singleton = One : (D.zero, 'g) D.suc is_singleton
type _ is_suc = Is_suc : 'n D.t * ('n, 'one, 'm) D.plus * 'one is_singleton -> 'm is_suc

let suc_pos : type n. n D.pos -> n is_suc = fun (Pos (n, g)) -> Is_suc (n, Suc (Zero, g), One)

let zero_nonsingleton : type c. D.zero is_singleton -> c = function
  | _ -> .
