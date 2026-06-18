type 'a t = Unit : unit t

let compare : type a b. a t -> b t -> (a, b) Eq.compare =
 fun a b ->
  match (a, b) with
  | Unit, Unit -> Eq
