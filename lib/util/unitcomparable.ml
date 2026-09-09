type 'a t = Unit : unit t

let compare : type a b. a t -> b t -> (a, b) Eq.compare =
 fun a b ->
  match (a, b) with
  | Unit, Unit -> Eq

(* There is only one generator, so no two are apart, and Unitcomparable is trivially Decidable. *)
type ('g1, 'g2) apart = |

type (_, _) decision =
  | Same : ('g, 'g) decision
  | Distinct : ('g1, 'g2) apart -> ('g1, 'g2) decision

let decide : type a b. a t -> b t -> (a, b) decision =
 fun a b ->
  match (a, b) with
  | Unit, Unit -> Same

let apart_irrefl : type g. (g, g) apart -> Empty.t = function
  | _ -> .
