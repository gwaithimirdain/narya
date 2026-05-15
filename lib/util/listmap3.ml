open Signatures

(* A simple implementation of MAP3_MAKER that uses heterogeneous association lists, applicable to any Quiver of triply-parametrized keys.  This is the direct analogue of Listmap.Map for keys whose type has three parameters (source, morphism, target). *)

module Map (Key : Category.Quiver) : MAP3_MAKER with module Key = Key = struct
  module Key = Key

  module Make (F : Fam4) = struct
    module F = F

    type _ t =
      | [] : 'p t
      | ( :: ) : (('a, 'b, 'c) Key.t * ('p, 'a, 'b, 'c) F.t) * 'p t -> 'p t

    let empty = []

    let rec find_opt : type a b c p. (a, b, c) Key.t -> p t -> (p, a, b, c) F.t option =
     fun k -> function
      | [] -> None
      | (l, x) :: xs -> (
          match Key.compare k l with
          | Eq -> Some x
          | Neq -> find_opt k xs)

    let add : type a b c p. (a, b, c) Key.t -> (p, a, b, c) F.t -> p t -> p t =
     fun k y xs ->
      let open Monad.Ops (Monad.Maybe) in
      let rec go = function
        | [] -> None
        | (l, x) :: xs -> (
            match Key.compare k l with
            | Eq -> Some ((l, y) :: xs)
            | Neq ->
                let* ys = go xs in
                return ((l, x) :: ys)) in
      match go xs with
      | Some ys -> ys
      | None -> (k, y) :: xs

    let update : type a b c p.
        (a, b, c) Key.t -> ((p, a, b, c) F.t option -> (p, a, b, c) F.t option) -> p t -> p t =
     fun k f xs ->
      let open Monad.Ops (Monad.Maybe) in
      let rec go = function
        | [] -> None
        | (l, x) :: xs -> (
            match Key.compare k l with
            | Eq -> (
                match f (Some x) with
                | Some y -> Some ((l, y) :: xs)
                | None -> Some xs)
            | Neq ->
                let* ys = go xs in
                return ((l, x) :: ys)) in
      match go xs with
      | Some ys -> ys
      | None -> (
          match f None with
          | Some y -> (k, y) :: xs
          | None -> xs)

    let rec remove : type a b c p. (a, b, c) Key.t -> p t -> p t =
     fun k -> function
      | [] -> []
      | (l, x) :: xs -> (
          match Key.compare k l with
          | Eq -> xs
          | Neq -> (l, x) :: remove k xs)

    type 'p mapper = {
      map : 'a 'b 'c. ('a, 'b, 'c) Key.t -> ('p, 'a, 'b, 'c) F.t -> ('p, 'a, 'b, 'c) F.t;
    }

    let rec map : type p. p mapper -> p t -> p t =
     fun f -> function
      | [] -> []
      | (k, x) :: xs -> (k, f.map k x) :: map f xs

    type 'p iterator = { it : 'a 'b 'c. ('a, 'b, 'c) Key.t -> ('p, 'a, 'b, 'c) F.t -> unit }

    let rec iter : type p. p iterator -> p t -> unit =
     fun f -> function
      | [] -> ()
      | (k, x) :: xs ->
          f.it k x;
          iter f xs
  end
end
