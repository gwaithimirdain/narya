open Dim
open Reporter
open Value
open Norm

(* At certain points we have to "un-act" on a synthesized type to get a type of which it might be a degeneracy of.  Currently we only try to do this if the arity is nonzero 0, in which case we can "cheat" by just grabbing one of the zero-dimensional boundaries, which is a normal, and taking its type. *)
let unact_ty : type n. err:Code.t -> kinetic value -> n D.t -> kinetic value =
 fun ~err ty n ->
  let (Full_tube tyargs) = get_tyargs ty "argument of redex" in
  (* We may need to extend the dimension n to match the dimension of the tyargs. *)
  match factor (TubeOf.inst tyargs) n with
  | None ->
      fatal (Insufficient_dimension { needed = n; got = TubeOf.inst tyargs; which = "function" })
  | Some (Factor nk) -> (
      let s = vertex n <|> err in
      let sk = sface_plus s nk (D.zero_plus (D.plus_right nk)) in
      match pface_of_sface sk with
      | `Proper fa -> (TubeOf.find tyargs fa).ty
      | `Id Eq -> ty)
