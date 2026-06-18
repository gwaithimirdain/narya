open Signatures

(* A simple implementation of MAP_MAKER that uses heterogeneous association lists, applicable to any Comparable notion of key. *)

module Map (Key : Comparable) : MAP_MAKER with module Key = Key = struct
  module Key = Key

  module Make (F : Fam2) = struct
    module F = F

    type _ t = [] : 'b t | ( :: ) : ('m Key.t * ('b, 'm) F.t) * 'b t -> 'b t

    let empty = []

    let rec find_opt : type k a. k Key.t -> a t -> (a, k) F.t option =
     fun k -> function
      | [] -> None
      | (l, x) :: xs -> (
          match Key.compare k l with
          | Eq -> Some x
          | Neq -> find_opt k xs)

    let add : type k a. k Key.t -> (a, k) F.t -> a t -> a t =
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

    let update : type k a. k Key.t -> ((a, k) F.t option -> (a, k) F.t option) -> a t -> a t =
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

    let rec remove : type k b. k Key.t -> b t -> b t =
     fun k -> function
      | [] -> []
      | (l, x) :: xs -> (
          match Key.compare k l with
          | Eq -> xs
          | Neq -> (l, x) :: remove k xs)

    type 'a mapper = { map : 'g. 'g Key.t -> ('a, 'g) F.t -> ('a, 'g) F.t }

    let rec map : type a. a mapper -> a t -> a t =
     fun f -> function
      | [] -> []
      | (k, x) :: xs -> (k, f.map k x) :: map f xs

    type 'a iterator = { it : 'g. 'g Key.t -> ('a, 'g) F.t -> unit }

    let rec iter : type a. a iterator -> a t -> unit =
     fun f -> function
      | [] -> ()
      | (k, x) :: xs ->
          f.it k x;
          iter f xs
  end
end
