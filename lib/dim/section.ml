open Util
open Deg
open Perm
open Face

(* If the arity is at least one, any degeneracy has a section that's a non-strict face. *)
let rec section_of_deg : type m n. (m, n) deg -> (n, m) face option =
 fun s ->
  let open Monad.Ops (Monad.Maybe) in
  let (Wrap l) = Endpoints.wrapped () in
  match (dom_deg s, Endpoints.len l) with
  | Nat Zero, _ ->
      let (Zero _) = s in
      return (Face (Zero, Zero))
  | Nat (Suc _), Nat (Suc _) -> (
      match deg_coresidual s Now with
      | Coresidual_zero s' ->
          let* (Face (f, p)) = section_of_deg s' in
          return (Face (End (f, (l, Top)), p))
      | Coresidual_suc (s', i) ->
          let* (Face (f, p)) = section_of_deg s' in
          return (Face (Mid f, Suc (p, i))))
  | _ -> None
