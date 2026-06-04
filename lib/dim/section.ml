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
  | Word Zero, _ ->
      let (Zero _) = s in
      return (Face (Zero, Zero))
  | Word (Suc (_, Unit)), N.Nat (Suc _) -> (
      match deg_coresidual s Now with
      | Coresidual_zero s' ->
          let* (Face (f, p)) = section_of_deg s' in
          return (Face (End (f, D.deg, (l, Top)), p))
      | Coresidual_suc (s', g_cs, i) -> (
          (* TODO: bridge to the input deg's outer generator; in a multi-generator world the generator structure should flow through deg_coresidual's result type. *)
          match D.G.compare g_cs D.deg with
          | Neq -> None
          | Eq ->
              let* (Face (f, p)) = section_of_deg s' in
              return (Face (Mid (f, g_cs), Suc (p, g_cs, i)))))
  | _ -> None
