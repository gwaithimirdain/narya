type 'a t = Unit : unit t

let compare : type a b. a t -> b t -> (a, b) Eq.compare =
 fun a b ->
  match (a, b) with
  | Unit, Unit -> Eq

let decide : type a b. a t -> b t -> ((a, b) Eq.t, (a, b) Eq.neq) Either.t =
 fun a b ->
  match (a, b) with
  | Unit, Unit -> Left Eq
