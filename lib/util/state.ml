(* This is a copied version of Algaeff.State that includes try_with, since a version of algaeff with that that hasn't been released yet.  *)

module Make (State : sig
  type t
end) =
struct
  type _ Effect.t += Get : State.t Effect.t | Set : State.t -> unit Effect.t

  let get () = Effect.perform Get
  let set st = Effect.perform (Set st)

  let run ~(init : State.t) f =
    let open Effect.Deep in
    let st = ref init in
    try f () with
    | effect Get, k -> continue k !st
    | effect Set v, k ->
        st := v;
        continue k ()

  let try_with ?(get = get) ?(set = set) f =
    let open Effect.Deep in
    try f () with
    | effect Get, k -> continue k (get ())
    | effect Set v, k ->
        set v;
        continue k ()

  let modify f = set @@ f @@ get ()

  let register_printer f =
    Printexc.register_printer @@ function
    | Effect.Unhandled Get -> f `Get
    | Effect.Unhandled (Set state) -> f (`Set state)
    | _ -> None

  let () = register_printer @@ fun _ -> Some "Unhandled myalgaeff effect; use Algaeff.State.run"
end
