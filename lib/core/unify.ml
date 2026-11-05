(* Unification: solving unification metavariables by comparing them with other values.  For now, we only implement the simplest case. *)

open Bwd
open Modal
open Dim
open Reporter
open Term
open Value
open Norm
open Act
open Domvars
open Readback

(* Try to solve a unification metavariable u with a value v, which are being compared in a context, at a type if known.  We can do this if u is a neutral unification metavariable with an identity insertion, and an environment and arguments that are a renaming (see Readback.renamed_ctx), and v reads back in the corresponding renamed context without containing u or any undefined variable (see Readback.Unifying).  Then the solution, substituted into u's environment, is v. *)
let try_solve_direct : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, kinetic) value option ->
    bool =
 fun ctx u v ty ->
  match u with
  | Neu { head = Live (Meta { meta; kind = Unif_meta unif as kind; env; ins }); args; ty = uty; _ }
    -> (
      match (is_id_ins ins, arg_spine args, v) with
      | None, _, _ | _, None, _ -> false
      (* Two occurrences of the same metavariable are compared by their environments and arguments instead. *)
      | Some _, Some _, Neu { head = Live (Meta { meta = meta'; _ }); _ }
        when match Meta.compare meta meta' with
             | Eq -> true
             | Neq -> false -> false
      | Some _, Some Eq, _ -> (
          (Global.unif_status meta unif = `Unsolved && Global.unif_assignable meta)
          &&
          let mty = Global.meta_ty meta kind in
          match renamed_ctx meta ctx env args mty (Global.unif_ctx meta) v with
          | None -> false
          | Some (Renamed_ctx { ctx = rctx; check_type; wrap; contracted }) -> (
              (* If we don't know the type at which they are being compared, we must check that the type of v is that of u. *)
              let typed =
                match ty with
                | Some _ -> true
                | None -> (
                    match v with
                    | Neu { ty = vty; _ } -> (
                        match Equal.equal_val ctx (Lazy.force vty) (Lazy.force uty) with
                        | Ok () -> true
                        | Error _ -> false)
                    | _ -> false) in
              typed
              &&
              (* If we can eta-contract, we do.  Otherwise, we read back v at the type of u, which has been substituted by its environment and arguments and hence lives in the current context like v. *)
              let solution =
                match List.find_map (fun attempt -> attempt ()) contracted with
                | Some _ as tm -> tm
                | None ->
                    Option.map wrap
                      (readback_unif_solution meta rctx ~check_type v (Lazy.force uty)) in
              match solution with
              | Some tm ->
                  Global.solve_unif meta tm;
                  true
              | None -> false)))
  | _ -> false

(* The inverse of the permutation represented by a nonidentity insertion. *)
let inverse_of_ins : type a b c. (a, b, c) insertion -> any_deg option =
 fun ins ->
  match is_id_ins ins with
  | Some _ -> None
  | None ->
      let (Perm_to p) = perm_of_ins ins in
      Some (Any_deg (deg_of_perm (perm_inv p)))

(* The permutation that removes all the insertions from a metavariable applied to arguments.  Acting on an application by a permutation composes it with the insertion of that application, and then pushes the part of the result that acts on the function inside, where it composes with the next insertion and also permutes the arguments.  Thus, we start from the outside by undoing the outermost insertion, and follow that by the permutation that undoes the rest, which is extended by an identity on the dimensions of the output.  We return None if there is nothing to undo, or if the spine contains anything other than arguments. *)
let rec inverse_of_spine : type a b c hmode mode any.
    (a, b, c) insertion -> (hmode, mode, any, live) apps -> any_deg option =
 fun ins args ->
  match args with
  | Emp -> inverse_of_ins ins
  | Snoc (rest, Arg (_, _, argins)) -> (
      match (inverse_of_ins argins, inverse_of_spine ins rest) with
      | None, inner -> inner
      | outer, None -> outer
      | Some (Any_deg outer), Some (Any_deg inner) ->
          let (DegExt (_, _, s)) = comp_deg_extending outer inner in
          Some (Any_deg s))
  | Snoc (_, Field _) | Snoc (_, Inst _) -> None

(* Try to solve a unification metavariable that may have permutations on it or on its arguments, as in "sym ?m" or "(sym ?f) x".  Since a permutation is invertible, the equation "p ?m = v" is equivalent to "?m = p⁻¹ v", which has the same solutions and which we can try to solve directly, at the type acted on by the same permutation.  This may also permute the arguments, but permuted variables are still a renaming.  If the type wasn't known then we must check that the types agree before acting on v, since it might not have enough dimensions otherwise. *)
let try_solve : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, kinetic) value option ->
    bool =
 fun ctx u v ty ->
  match u with
  | Neu { head = Live (Meta { kind = Unif_meta _; ins; _ }); args; ty = uty; _ } -> (
      match inverse_of_spine ins args with
      | None -> try_solve_direct ctx u v ty
      | Some (Any_deg pinv) -> (
          let ty =
            match (ty, v) with
            | Some _, _ -> ty
            | None, Neu { ty = vty; _ } -> (
                match Equal.equal_val ctx (Lazy.force vty) (Lazy.force uty) with
                | Ok () -> Some (Lazy.force uty)
                | Error _ -> None)
            | None, _ -> None in
          match ty with
          | None -> false
          | Some ty ->
              let idc = Modalcell.id2 (Ctx.mode ctx) in
              try_solve_direct ctx (act_value u pinv idc) (act_value v pinv idc)
                (Some (gact_ty None ty pinv idc))))
  | _ -> try_solve_direct ctx u v ty

(* A metavariable that is projected from, perhaps after being applied to some arguments, has to be solved by a tuple, since we can only get information about one field from the projection, and the other fields have to be left unknown.  This is always correct, by eta-conversion, so it doesn't affect whether the solution is most general; but it does create more metavariables, so we do it only when solving an equation that requires it.  To avoid having to duplicate the logic for typechecking tuples, particularly regarding modal fields (whose components live in a locked context, and possibly a different mode), we do this by constructing a raw term out of abstractions, tuples, and placeholders, and typechecking it at the type of the metavariable.  Since typechecking comes later, we record here just the shape of the term, consisting of an abstraction for each argument (with a name, and whether it is a cube abstraction), a tuple for each projection (with all the field names and the one that continues), and a permutation wherever the occurrence of the metavariable has one, since then the term that is projected from is that permutation of the metavariable and hence the metavariable must be its inverse acting on a tuple.  There is no need for a final sequence of abstractions, since the metavariables created for the tuple components can just be applied to the same arguments. *)
type expansion =
  | Abs : string option * bool -> expansion
  | Tuple : string list * string -> expansion
  | Perm : ('m, 'n) deg -> expansion

type expander = {
  expand :
    'mode 'a 'b.
    ('mode, 'a, 'b) Ctx.t -> ('mode, kinetic) value -> expansion list -> ('mode, 'b, kinetic) term;
}

let expander : expander ref =
  ref { expand = (fun _ _ _ -> fatal (Anomaly "unification not installed")) }

(* The names of the fields that a tuple at a record type must have, at some dimension.  A modal field whose modality is nonparametric disappears at a dimension it filters nontrivially, and must be omitted. *)
let field_names : type mode a m n et.
    (mode * a * D.zero * n * et) Term.CodatafieldAbwd.t -> m D.t -> string list =
 fun fields m ->
  Bwd.fold_right
    (fun (Term.CodatafieldAbwd.Entry (f, Codatafield (_, Adjunction { left; _ }, _, _))) names ->
      let (Has_filter filter) = Modality.filter left m in
      match Modality.filter_is_trivial m filter with
      | Some _ -> Field.to_string f :: names
      | None -> names)
    fields []

(* Compute the shape of the expansion needed by a metavariable with an application spine, given the value of the metavariable with no spine, if it is possible.  We replay the spine on that value in order to be able to compute the type at each point. *)
let expansion_shape : type hmode mode any.
    (hmode, kinetic) value ->
    expansion list ->
    (hmode, mode, any, live) apps ->
    expansion list option =
 fun head start args ->
  let exception Stuck in
  let tyof : type m. (m, kinetic) value -> m View.view_type = function
    | Neu { ty; _ } -> view_type ~severity:Asai.Diagnostic.Error (Lazy.force ty) "expansion_shape"
    | _ -> raise_notrace Stuck in
  let rec go : type m any. (hmode, m, any, live) apps -> (m, kinetic) value * expansion list =
    function
    | Emp -> (head, start)
    | Snoc (args, entry) ->
        let cur, shape = go args in
        let shape =
          match entry with
          | Arg (_, xs, ins) -> (
              match tyof cur with
              | Canonical (_, Pi { x; _ }, _, _) -> (
                  let cube =
                    match D.compare_zero (CubeOf.dim xs) with
                    | Zero -> false
                    | Pos _ -> true in
                  let shape = Abs (option_of_binder_name (top_variable x), cube) :: shape in
                  match inverse_of_ins ins with
                  | Some (Any_deg pinv) -> Perm pinv :: shape
                  | None -> shape)
              | _ -> raise_notrace Stuck)
          | Field (_, fld, _, _) -> (
              match tyof cur with
              | Canonical (_, Codata { eta = Eta; fields; _ }, ins, _) ->
                  Tuple (field_names fields (cod_left_ins ins), Field.to_string fld) :: shape
              | _ -> raise_notrace Stuck)
          | Inst _ -> raise_notrace Stuck in
        let (Val next) = app_eval_entry (Val cur) entry in
        (next, shape) in
  let rec trim = function
    | (Abs _ | Perm _) :: shape -> trim shape
    | shape -> shape in
  try
    match trim (snd (go args)) with
    | [] -> None
    | shape -> Some (List.rev shape)
  with Stuck -> None

(* Expand a unification metavariable that is projected from, and then compare the result to the other value. *)
let try_expand : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    (mode, kinetic) value ->
    (mode, kinetic) value option ->
    bool =
 fun ctx u v ty ->
  match u with
  | Neu { head = Live (Meta { meta; kind = Unif_meta unif as kind; env; ins }); args; _ } -> (
      match (arg_spine args, v) with
      | Some _, _ -> false
      | _, Neu { head = Live (Meta { meta = meta'; _ }); _ }
        when match Meta.compare meta meta' with
             | Eq -> true
             | Neq -> false -> false
      | None, _ -> (
          (Global.unif_status meta unif = `Unsolved && Global.unif_assignable meta)
          &&
          let mctx = Global.unif_ctx meta in
          let head = eval_term env (Meta (meta, kind, Kinetic)) in
          (* A permutation on the metavariable itself only acts on the dimensions of its type if its environment doesn't contribute any others. *)
          let start =
            match (inverse_of_ins ins, D.compare_zero (cod_left_ins ins)) with
            | None, _ -> Some (head, [])
            | Some (Any_deg pinv), Zero ->
                let (Perm_to p) = perm_of_ins ins in
                Some (act_value head (deg_of_perm p) (Modalcell.id2 (Ctx.mode mctx)), [ Perm pinv ])
            | Some _, Pos _ -> None in
          Reporter.discard_errors ~fallback:(fun () -> false) @@ fun () ->
          match Option.bind start (fun (head, start) -> expansion_shape head start args) with
          | None -> false
          | Some shape -> (
              let mty = eval_term (Ctx.env mctx) (Global.meta_ty meta kind) in
              Global.solve_unif meta (!expander.expand mctx mty shape);
              (* Now u has a value, whose head is a metavariable created for a tuple component, so we can try again to solve that. *)
              let result =
                match ty with
                | Some ty -> Equal.equal_at ctx (view_term u) v ty
                | None -> Equal.equal_val ctx (view_term u) v in
              match result with
              | Ok () -> true
              | Error _ -> false)))
  | _ -> false

(* A type is a singleton if any two of its elements are equal, by eta-conversion: this holds for records all of whose fields are singletons, and functions whose codomains are.  We test this by comparing two fresh variables, without solving any metavariables. *)
let is_singleton : type mode a b. (mode, a, b) Ctx.t -> (mode, kinetic) value -> bool =
 fun ctx ty ->
  let id = Modality.id (Ctx.mode ctx) in
  let filter = Modality.filter_zero id in
  let doms = CubeOf.singleton ty in
  let vars = singleton_variables D.zero (`Anon no_hints) in
  let xs, xnfs = dom_vars ctx id doms in
  let (Any_ctx ctx) = Ctx.variables_vis ctx filter vars xnfs in
  let ys, ynfs = dom_vars ctx id doms in
  let (Any_ctx ctx) = Ctx.variables_vis ctx filter vars ynfs in
  Reporter.discard_errors ~fallback:(fun () -> false) @@ fun () ->
  match
    Equal.flexibly (fun () -> Equal.equal_at ctx (CubeOf.find_top xs) (CubeOf.find_top ys) ty)
  with
  | Ok () -> true
  | Error _ -> false

(* An unsolved unification metavariable at a singleton type has a unique solution even if nothing has constrained it.  Without eta-expanding all metavariables when they are created, we have to find these at the end of a command.  We expand them one level, using the same mechanism as for field projections, which produces new metavariables at singleton types, until no more remain. *)
let rec solve_singletons () =
  let changed = ref false in
  Global.iter_unsolved_unifs
    {
      it =
        (fun meta ctx ty ->
          if Global.unif_assignable meta then
            let ety = eval_term (Ctx.env ctx) ty in
            if is_singleton ctx ety then
              let shape =
                match view_type ~severity:Asai.Diagnostic.Error ety "solve_singletons" with
                | Canonical (_, Pi { x; doms; _ }, _, _) ->
                    let cube =
                      match D.compare_zero (CubeOf.dim doms) with
                      | Zero -> false
                      | Pos _ -> true in
                    [ Abs (option_of_binder_name (top_variable x), cube) ]
                | Canonical (_, Codata { eta = Eta; fields; _ }, ins, _) -> (
                    let tuple = Tuple (field_names fields (cod_left_ins ins), "") in
                    (* If the record has a nonidentity insertion, it isn't actually a record type, but it is isomorphic to one by a permutation.  So its element is a tuple with that permutation acting on it. *)
                    match is_id_ins ins with
                    | Some _ -> [ tuple ]
                    | None ->
                        let (Perm_to p) = perm_of_ins ins in
                        [ Perm (deg_of_perm p); tuple ])
                | _ -> [] in
              match shape with
              | [] -> ()
              | _ :: _ ->
                  Global.solve_unif meta (!expander.expand ctx ety shape);
                  changed := true);
    };
  if !changed then solve_singletons ()

let install (expand : expander) =
  expander := expand;
  Global.set_singleton_unif_solver solve_singletons;
  Equal.solver :=
    {
      solve =
        (fun ctx x y ty ->
          (* We prefer not to expand, if the other side can be solved directly. *)
          try_solve ctx x y ty
          || try_solve ctx y x ty
          || try_expand ctx x y ty
          || try_expand ctx y x ty);
    }
