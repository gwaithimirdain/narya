open Bwd
open Util
open Modal
open Perhaps
open Tbwd
open Reporter
open Term
open Value
open Domvars
open Raw
open Dim
open Tctx
open Act
open Norm
open Equal
open Subtype
open Readback
open Degctx
open Printable
open Unact
open Asai.Range
include Status

module OracleData = struct
  type question = Ask : ('mode, 'a, 'b) Ctx.t * ('mode, kinetic) value -> question
  type answer = (unit, Code.t) Result.t
end

module Oracle = Query.Make (OracleData)

(* Check that a given value is a zero-dimensional non-modal type family (something where an indexed datatype could live) and return the length of its domain telescope (the number of indices).  Unfortunately I don't see an easy way to do this without essentially going through all the same steps of extending the context that we would do to check something at that type family.  Also check whether all of its domain types are either discrete or belong to the given set of constants. *)
let rec typefam : type mode a b.
    ?discrete:unit Constant.Map.t -> (mode, a, b) Ctx.t -> (mode, kinetic) value -> int * bool =
 fun ?discrete ctx ty ->
  match view_type ~severity:Asai.Diagnostic.Error ty "typefam" with
  | Canonical (_, UU (_, n), _, _) -> (
      match D.compare n D.zero with
      | Eq -> (0, true)
      | Neq -> fatal (Unimplemented "higher-dimensional datatypes"))
  | Canonical (_, Pi { x; filter; doms; cods }, _, tyargs) -> (
      let modality = Modality.filter_modality filter in
      (* In practice, these dimensions will always be zero also if the function succeeds, otherwise the eventual output would have to be higher-dimensional too.  But it doesn't hurt to be more general, and will require less change if we eventually implement higher-dimensional datatypes. *)
      match (D.compare (TubeOf.inst tyargs) (BindCube.dim cods), Modality.compare_id modality) with
      | Eq, Eq ->
          let newargs, newnfs = dom_vars ctx modality doms in
          let output = tyof_app cods tyargs filter newargs in
          let (Any_ctx newctx) =
            Ctx.variables_vis ctx (Modality.filter_idempotent filter) x newnfs in
          let n, d = typefam ?discrete newctx output in
          let disc =
            (* For indices of discrete datatypes, we only allow zero-dimensional pi-types. *)
            match D.compare (CubeOf.dim doms) D.zero with
            | Eq -> is_discrete ?discrete (CubeOf.find_top doms)
            | Neq -> false in
          (n + 1, d && disc)
      | Neq, _ -> fatal (Dimension_mismatch ("typefam", TubeOf.inst tyargs, CubeOf.dim doms))
      | _, Neq ->
          fatal
            (Modality_mismatch
               (`Internal, "indices of datatype", modality, Modality.id (Modality.tgt modality))))
  | _ -> fatal (Checking_canonical_at_nonuniverse ("datatype", PVal (ctx, ty)))

(* Given a multi-argument type family, and the type *of* that type family, both as values, and a context for them, compute the type of type families dependent *on* that family, as a term.  For example, if the arguments are

   x y z ↦ D x y z
   (x : A) (y : B x) (z : C x y) → Type

(as values), then the output will be

   (x : A) (y : B x) (z : C x y) (w : D x y z) → Type

(as a term).  However, although the indices of a datatype family themselves must be zero-dimensional, the type families involved here could be higher-dimensional, because they come from an *evaluation* of that datatype family which could be a higher-dimensional version of it.  In that case, the arguments are flattened out to a zero-dimensional family in the return value, so for instance if given

   x ⤇ B₂ x.2
   (x₀ : A₀) (x₁ : A₁) (x₂ : A₂ x₀ x₁) ⇒ Id Type (B₀ x₀) (B₁ x₁)

then the output will be

   (x₀ : A₀) (x₁ : A₁) (x₂ : A₂ x₀ x₁) (y₀ : B₀ x₀) (y₁ : B₁ x₁) (y₂ : B₂ x₂) → Type

In the modal case, there is a window modality, say μ : p → q, the inputs are at mode p, with all arguments NON-MODAL because in the context of use this is a datatype family with its indices, and indices cannot be modal.  However, the output is at mode q, depending modally on its arguments, since that is the motive of a match with window μ:

   (x :μ| A) (y :μ| B x) (z :μ| C x y) (w :μ| D x y z) → Type_q
   
   
*)
let rec motive_of_family : type dom window mode a b.
    (mode, a, b) Ctx.t ->
    (dom, window, mode) Modality.t ->
    (dom, kinetic) value ->
    (dom, kinetic) value ->
    (mode, b, kinetic) term =
 fun ctx window tm ty ->
  (* The motive's pi-type domains are window-modal, so their dimension filter is the (zero-dimensional) filter of the window modality. *)
  let filter = Modality.filter_zero window in
  (* First we define some auxiliary modules and traversal functions. *)
  let module S = struct
    type 'a suc = ('a, (window, D.zero) dim_entry) snoc
  end in
  let module F = struct
    type ('left, 'c, 'any) t =
      | Ftm :
          ('left, mode, window, dom, 'lw) plus_lock * (dom, 'lw, kinetic) term
          -> ('left, 'c, 'any) t
  end in
  let module FCube = Icube (S) (F) in
  let module C = struct
    type 'b t = (mode, 'b) Ctx.any
  end in
  let module T = struct
    type 'c t = (mode, 'c, kinetic) term
  end in
  let module MC = FCube.Traverse (C) in
  let module MT = FCube.Traverse (T) in
  let folder : type left m any.
      (left, m, any) F.t ->
      (left, (window, D.zero) dim_entry) snoc T.t ->
      left T.t * (left, m, any) F.t =
   fun (Ftm (left_plus, dom)) cod ->
    ( Pi
        {
          x = singleton_variables D.zero (`Anon no_hints);
          filter;
          doms = Modal (window, left_plus, CubeOf.singleton dom);
          cods = CodCube.singleton (Cod (filter, cod));
        },
      Ftm (left_plus, dom) ) in
  let builder : type left n m.
      n variables ->
      (n, dom Binding.t) CubeOf.t ->
      (m, n) sface ->
      left C.t ->
      (left, m, b) MC.fwrap_left =
   fun x newnfs fa (Any_ctx ctx) ->
    let (Locked (plus_window, wctx)) = Ctx.lock ctx window in
    let v = CubeOf.find newnfs fa in
    let cv = readback_val wctx (Binding.value v).ty in
    let name =
      match find_variable fa x with
      | `Named _ as x -> x
      | `Anon _ -> `Anon (View.hints_of_ty (Binding.value v).ty) in
    let (Any_ctx newctx) =
      (* TODO: In the case of a cube variable, should we be annotating the variable names by their face somehow?  *)
      Ctx.variables_vis ctx filter (singleton_variables D.zero name) (CubeOf.singleton v) in
    Fwrap (Ftm (plus_window, cv), Any_ctx newctx) in
  (* We start by inspecting the type of the family passed. *)
  match view_type ty "motive_of_family" with
  | Canonical (_, Pi { x; filter = ffilter; doms; cods }, ins, tyargs) -> (
      (* The type family itself must be non-modal (any modal window is carried separately). *)
      match Modality.compare_id (Modality.filter_modality ffilter) with
      | Neq -> fatal (Anomaly "modal family in motive_of_family")
      | Eq ->
          let Eq = eq_of_ins_zero ins in
          let newvars, newnfs = dom_vars ctx window doms in
          (* We extend the context, not by the cube of types of newnfs, but by its elements one at a time as singletons.  This is because we want eventually to construct a 0-dimensional pi-type.  As we go, we also read back these types and store them to later take the pi-type over.  Since they are all in different contexts, and we need to keep track of the type-indexed checked length of those contexts to ensure the later pis are well-typed, we use an indexed cube indexed over Tctxs. *)
          let (Wrap (newdoms, Any_ctx newctx)) =
            MC.build_left (CubeOf.dim newnfs)
              { build = (fun fa ctx -> builder x newnfs fa ctx) }
              (Any_ctx ctx) in
          (* Now we recurse into the codomain of the pi-type, having applied the type family itself to the new variables we introduced. *)
          let newtm = apply_term tm ffilter newvars in
          let motive = motive_of_family newctx window newtm (tyof_app cods tyargs ffilter newvars) in
          (* Finally, we postprocess that result by adding the pi-type domains we computed for this argument. *)
          let motive, _ = MT.fold_map_right { foldmap = (fun _ x y -> folder x y) } newdoms motive in
          motive)
  | Canonical (_, UU _, _, tyargs) ->
      (* We've reached the end of the function domains in the type of our type family.  We thus have one more domain to abstract over: the datatype itself, which is now the *term* we were passed in this version, along with all its boundaries, which are the instantiation arguments of the universe it belongs to. *)
      let doms = TubeOf.plus_cube (val_of_norm_tube tyargs) (CubeOf.singleton tm) in
      let _, newnfs = dom_vars ctx window doms in
      let m = CubeOf.dim newnfs in
      let (Wrap (newdoms, _)) =
        MC.build_left m
          { build = (fun fa ctx -> builder (singleton_variables m (`Anon no_hints)) newnfs fa ctx) }
          (Any_ctx ctx) in
      (* The result is a pi-type over all those domains, whose codomain is just the universe. *)
      let motive, _ =
        MT.fold_map_right
          { foldmap = (fun _ x y -> folder x y) }
          newdoms
          (UU (Ctx.mode ctx, D.zero)) in
      motive
  | _ -> fatal (Anomaly "non-family in motive_of_family")

type (_, _, _) vars_of_names =
  | Vars :
      ('a, 'b, 'abc) N.plus * (N.zero, 'n, binder_name, 'b) NICubeOf.t
      -> ('a, 'abc, 'n) vars_of_names

let vars_of_names : type a c abc n.
    Asai.Range.t option -> n D.t -> (a, c, abc) Namevec.t -> (a, abc, n) vars_of_names =
 fun loc dim xs ->
  let module S = struct
    type 'b t = Ok : (a, 'b, 'ab) N.plus * ('ab, 'c, abc) Namevec.t -> 'b t | Missing of int
  end in
  let module Build = NICubeOf.Traverse (S) in
  match
    Build.build_left dim
      {
        build =
          (fun _ -> function
            | Ok (ab, x :: xs) -> Fwrap (NFamOf (binder_name_of_option x), Ok (Suc ab, xs))
            | Ok _ -> Fwrap (NFamOf (`Anon no_hints), Missing (-1))
            | Missing j -> Fwrap (NFamOf (`Anon no_hints), Missing (j - 1)));
      }
      (Ok (Zero, xs))
  with
  | Wrap (names, Ok (ab, [])) -> Vars (ab, names)
  | Wrap (_, Ok (_, xs)) -> fatal ?loc (Wrong_boundary_of_record (Fwn.to_int (Namevec.length xs)))
  | Wrap (_, Missing j) -> fatal ?loc (Wrong_boundary_of_record j)

(* Slurp up an entire application spine.  Returns the function, and all the arguments, where each argument is paired with the location of its application.  So spine "f x y" would return "f" (located) along with [(location of "f x", "x" (located)); (location of "f x y", "y" (located))]. *)
let spine : type a.
    a check located ->
    a check located
    * (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list =
 fun tm ->
  let rec spine tm args =
    match tm.value with
    | Synth (App (fn, arg, impl)) -> spine fn ((tm.loc, arg, impl) :: args)
    | _ -> (tm, args) in
  spine tm []

(* Pull all the actions off of a term and compose them. *)
let rec actions : type a. a check located option -> any_deg * a check located option =
 fun tm ->
  match tm with
  | Some { value = Synth (Act (_, s, tm)); _ } ->
      let Any_deg s', tm = actions tm in
      let (DegExt (_, _, ss')) = comp_deg_extending s' s in
      (Any_deg ss', tm)
  | _ -> (Any_deg (id_deg D.zero), tm)

(* Temporarily define a given head (constant or meta) to be a given value, in executing a callback.  However, if an error has occurred earlier in typechecking other parts of it, then instead bind that head to an error value that doesn't allow it to be used. *)
let run_with_definition : type mode a c.
    (mode, a) potential_head ->
    (mode, a, potential) term ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    (unit -> c) ->
    c =
 fun head tm errs f ->
  match (head, errs) with
  (* In the case of an error, we bind the head to the error "Accumulated Emp".  That has the effect that accesses to it fail, but aren't displayed to the user as anything, since what's really going on is that we refuse to even try to typecheck later parts of a term that depend on previous parts that already failed, and this "error" is just detecting that dependence. *)
  (* We ignore the substituted dimension of the head, since this is really setting the *global* definition, which is not substituted. *)
  | Constant (c, mode, _), Emp -> Global.with_definition c mode (`Defined tm) f
  | Constant (c, _, _), Snoc _ -> Global.without_definition c (Accumulated ("dependence", Emp)) f
  | Meta (m, _), Emp -> Global.with_meta_definition m tm f
  | Meta (m, _), Snoc _ -> Global.without_meta_definition m (Accumulated ("dependence", Emp)) f

let unless_error (v : 'a) (err : 'b Bwd.t) : ('a, Code.t) Result.t =
  match err with
  | Emp -> Ok v
  | Snoc _ -> Error (Accumulated ("dependence", Emp))

(* A "checkable branch" stores all the information about a branch in a match, both that coming from what the user wrote in the match and what is stored as properties of the datatype.  *)
type (_, _, _, _) checkable_branch =
  | Checkable_branch : {
      xs : ('a, 'c, 'ac) Namevec.t;
      (* If the body is None, that means the user omitted this branch.  (That might be ok, if it can be refuted by a pattern variable belonging to an empty type.) *)
      body : 'ac check located option;
      env : ('mode, 'm, 'b) env;
      argtys : ('mode, 'b, 'c, 'bc) Telescope.t;
      index_terms : (('mode, 'bc, kinetic) term, 'ij) Vec.t;
    }
      -> ('mode, 'a, 'm, 'ij) checkable_branch

(* A "synthable branch" is similar, but records the fact that the user gave a synthesizing term.  *)
type (_, _, _, _) synthable_branch =
  | Synthable_branch : {
      xs : ('a, 'c, 'ac) Namevec.t;
      body : 'ac synth located;
      env : ('mode, 'm, 'b) env;
      argtys : ('mode, 'b, 'c, 'bc) Telescope.t;
      index_terms : (('mode, 'bc, kinetic) term, 'ij) Vec.t;
    }
      -> ('mode, 'a, 'm, 'ij) synthable_branch

(* This preprocesssing step pairs each user-provided branch with the corresponding constructor information from the datatype.  Curiously, the only mode parameter that appears here is the *source* of the window modality, i.e. the mode at which the datatype and discriminee live. *)
let merge_branches : type hmode dom a m ij.
    hmode head ->
    (Constr.t, a branch) Abwd.t ->
    (Constr.t, (dom, m, ij) Value.dataconstr) Abwd.t ->
    (Constr.t * (dom, a, m, ij) checkable_branch) list =
 fun head user_branches data_constrs ->
  let user_branches, leftovers =
    Bwd.fold_left
      (fun ((userbrs, databrs) :
             (Constr.t, (dom, a, m, ij) checkable_branch) Abwd.t
             * (Constr.t, (dom, m, ij) Value.dataconstr) Abwd.t)
           (constr, Branch ({ value = xs; loc }, cube, body)) ->
        (* We check at the preprocessing stage that there are no duplicate constructors in the match. *)
        if Abwd.mem constr userbrs then fatal ?loc (Duplicate_constructor_in_match constr);
        let databrs, databr = Abwd.extract constr databrs in
        let (Value.Dataconstr { env; args = argtys; indices = index_terms }) =
          match databr with
          | Some db -> db
          | None -> fatal ?loc (No_such_constructor_in_match (phead head, constr)) in
        (* Check that the abstraction symbol matches the dimension of the discriminee. *)
        (match (cube, D.compare_zero (dim_env env)) with
        | `Normal loc, Pos _ ->
            fatal ?loc (Noncube_abstraction_in_higher_dimensional_match (dim_env env))
        | `Normal _, Zero -> ()
        (* Cube abstractions ⤇ can be used with 0-dimensional discriminees if they're generated as part of a multiple/deep match clause that also includes some higher discriminess.  We check for errors in that when the outer match finishes. *)
        | `Cube _, Zero -> ()
        | `Cube bs, Pos _ -> List.iter (fun b -> b.value := true) bs);
        (* We also check during preprocessing that the user has supplied the right number of pattern variable arguments to the constructor.  The positive result of this check is then recorded in the common existential types bound by Checkable_branch. *)
        match Fwn.compare (Namevec.length xs) (Telescope.length argtys) with
        | Neq ->
            fatal ?loc
              (Wrong_number_of_arguments_to_pattern
                 (constr, Fwn.to_int (Namevec.length xs) - Fwn.to_int (Telescope.length argtys)))
        | Eq ->
            let br = Checkable_branch { xs; body = Some body; env; argtys; index_terms } in
            (Snoc (userbrs, (constr, br)), databrs))
      (Bwd.Emp, data_constrs) user_branches in
  (* If there are any constructors in the datatype left over that the user didn't supply branches for, we add them to the list at the end.  They will be tested for refutability. *)
  Bwd.prepend user_branches
    (Bwd_extra.to_list_map
       (fun (c, Value.Dataconstr { env; args = argtys; indices = index_terms }) ->
         let b = Telescope.length argtys in
         let (Bplus plus_args) = Raw.Indexed.bplus b in
         let xs = Namevec.none plus_args in
         (c, Checkable_branch { xs; body = None; env; argtys; index_terms }))
       leftovers)

exception Case_tree_construct_in_let

(* The output of checking a telescope includes an extended context. *)
type (_, _, _, _, _) checked_tel =
  | Checked_tel :
      ('mode, 'b, 'c, 'bc) Telescope.t * ('mode, 'ac, 'bc) Ctx.t
      -> ('mode, 'a, 'b, 'c, 'ac) checked_tel

(* A telescope of metavariables instead of types.  Created from a telescope of types by make_letrec_metas. *)
type (_, _, _, _) meta_tel =
  | Nil : ('mode, 'b, Fwn.zero, 'b) meta_tel
  | Ext :
      string option
      * ('mode, 'a, 'b, potential) Meta.t
      (* Letrec metavariables can't be modal. *)
      * ('mode, ('b, ('mode id, D.zero) dim_entry) snoc, 'c, 'bc) meta_tel
      -> ('mode, 'b, 'c Fwn.suc, 'bc) meta_tel

(* In HOTT mode, the user isn't allowed to define gel-types, so we bail out at typechecking time if we detect one.  But in parametricity mode, and when bootstrapping the definition of glue, we set this flag to true. *)
let gel_ok = ref false

(* Polymorphic callback for computing the motive of a non-refining match.  See check_branches for general explanation.  (For thought: instead of callbacks that use an existential type wrapped in a GADT, this could perhaps also be modeled using multiple classes that implement the same interface, and that might be more ergonomic.) *)
type (_, _, _, _, _) match_motive =
  | Motive : {
      (* GIVEN *)
      get :
        'm 'ij.
        (* the dimension of the match, *)
        'm D.t ->
        (* the list of branches remaining to be typechecked, and *)
        (Constr.t * ('dom, 'a, 'm, 'ij) checkable_branch) list ->
        (* the datatype family, applied to its parameters but not its indices, *)
        'dom normal Lazy.t option ref ->
        (* RETURN *)
        (* the motive of the match (or failure) -- note this is an abstract type, only unpackable by "use" below. *)
        'motive option
        (* a list of errors produced by trying to find that motive *)
        * Code.t Asai.Diagnostic.t Bwd.t
        (* a map of branches that were typechecked in the process of looking for the motive *)
        * ('mode, 'b, 'm) Term.branch Constr.Map.t
        (* and a list of branches that haven't yet been typechecked. *)
        * (Constr.t * ('dom, 'a, 'm, 'ij) checkable_branch) list;
      (* GIVEN *)
      use :
        'm 'bc 'ij.
        (* a match motive, which can only have been computed by "get" above *)
        'motive ->
        (* the constructor labeling a particular branch *)
        Constr.t ->
        (* the dimension of the match *)
        'm D.t ->
        (* a vector of values for the type indices in this branch *)
        (('dom, 'bc, kinetic) term, 'ij) Vec.t ->
        (* the environment in which the datatype was evaluated, extended by new pattern variables for the arguments of the constructor in this branch. *)
        ('dom, 'm, 'bc) env ->
        (* The new pattern variables as values, along with their boundaries.  MODALTODO: should perhaps the modalities be recorded here to match those of the constructor arguments? *)
        ('m, 'dom, kinetic) modal_value_cube list ->
        (* RETURN the actual motive type against which to typecheck this branch. *)
        ('mode, kinetic) value;
      (* GIVEN *)
      return :
        'm 'mn 'ij.
        (* the values of the datatype indices at the discriminee *)
        (('m, 'dom normal) CubeOf.t, 'ij) Vec.t ->
        (* the instantiation arguments of the datatype at the discriminee *)
        (D.zero, 'mn, 'mn, 'dom normal) TubeOf.t ->
        (* the match motive, as computed by "get" above *)
        'motive ->
        (* RETURN the type of the match term, i.e. the motive evaluated (if it is dependent) at these indices, boundary, and the discriminee itself.  (The discriminee doesn't have to be passed as an argument to this callback explicitly because it is available when the callback is defined as a closure.)  *)
        ('mode, kinetic) value;
    }
      -> ('dom, 'window, 'mode, 'a, 'b) match_motive

(* Get a window modality if one was supplied, defaulting to the identity if not. *)
let get_window mode = function
  | Some w -> (
      match Modality.of_name_tgt mode w.value with
      | Error e -> modality_fatal "checking let-in" (e :> modality_error)
      | Ok w -> w)
  | None -> Wrap (Modality.id mode)

(* Resolve the recursion verdict of a datatype by chasing the recorded verdicts of any blocking metavariables through Global, just as evaluation of a term containing metavariables consults their definitions.  A hole that has been solved has the verdict of its solution recorded; a still-unsolved hole remains unknown (and is treated conservatively as recursive by the window check, but nothing is cached, so a later check after solving it can succeed). *)
let rec chase_recursion : Positivity.recursion -> [ `Nonrecursive | `Recursive | `Unknown ] =
  function
  | `Nonrecursive -> `Nonrecursive
  | `Recursive -> `Recursive
  | `Unknown ms ->
      Meta.WrapSet.fold
        (fun (Meta.Wrap m) acc ->
          match acc with
          | `Recursive -> `Recursive
          | `Nonrecursive | `Unknown -> (
              let (df : _ Metadef.t) = Global.find_meta m in
              match df.tm with
              | `Defined _ -> (
                  match (chase_recursion df.recursion, acc) with
                  | `Recursive, _ | _, `Recursive -> `Recursive
                  | `Unknown, _ | _, `Unknown -> `Unknown
                  | `Nonrecursive, `Nonrecursive -> `Nonrecursive)
              | `Axiom | `Undefined -> `Unknown))
        ms `Nonrecursive

(* The identity window modality is always allowed; we special-case that so that mode theories don't have to worry about explicitly marking it as pellucid.  A window modality is always allowed if it is pellucid.  Otherwise, the datatype being matched against must have no recursive constructors, and the modality must be transparent, unless the datatype also has exactly one constructor, in which case translucent suffices. *)
let check_window_transparency : type dom window mode k a.
    (dom, window, mode) Modality.t -> (k, a) Abwd.t -> Positivity.recursion -> unit =
 fun window constrs recursive ->
  match Modality.compare_id window with
  | Eq -> ()
  | Neq -> (
      if Modality.pellucid window then ()
      else
        let single =
          match Abwd.bindings constrs with
          | [ _ ] -> true
          | _ -> false in
        match chase_recursion recursive with
        | `Nonrecursive when Modality.transparent window || (single && Modality.translucent window)
          -> ()
        | r -> fatal (Nontransparent_window_modality (window, single, r)))

(* Check a term or case tree (depending on the energy: terms are kinetic, case trees are potential).  The ?discrete parameter is supplied if the term we are currently checking might be a discrete datatype, in which case it is a set of all the currently-being-defined mutual constants.  Most term-formers are nondiscrete, so they can just ignore this argument and make their recursive calls without it. *)
let rec check : type mode a b s.
    ?discrete:unit Constant.Map.t ->
    (mode, b, s) status ->
    (mode, a, b) Ctx.t ->
    a check located ->
    (mode, kinetic) value ->
    (mode, b, s) term =
 fun ?discrete status ctx tm ty ->
  let go () : (mode, b, s) term =
    (* If the "type" is not a type here, or not fully instantiated, that's a user error, not a bug. *)
    let severity = Asai.Diagnostic.Error in
    match (tm.value, status) with
    (* A Let is a "synthesizing" term so that it *can* synthesize, but in checking position it checks instead. *)
    | Synth (Let (x, modality, v, body)), _ ->
        let clet, Not_some = synth_or_check_let status ctx x modality v body (Some ty) in
        clet
    | Synth (Letrec (vtys, vs, body)), _ ->
        let clet, Not_some = synth_or_check_letrec status ctx vtys vs body (Some ty) in
        clet
    | Synth (Act (str, fa, x) as stm), _ -> (
        (* An action can always synthesize, but can usually also check. *)
        match (perm_of_deg fa, x) with
        | Some pfa, Some x -> (
            (* It can check if its degeneracy is a pure permutation, since then the type of the argument can be inferred by applying the inverse permutation to the ambient type. *)
            let fainv = deg_of_perm (perm_inv pfa) in
            match
              Reporter.try_with ~fatal:(fun d ->
                  (* If the user has given a symmetrized term that synthesizes but doesn't match the checking type, we want the error reported to be Unequal_synthesized_type.  So we fall back to synthesizing if the checking type doesn't symmetrize.  *)
                  match d.message with
                  | Low_dimensional_argument_of_degeneracy _ -> Error d
                  | _ -> fatal_diagnostic d)
              @@ fun () ->
              Ok
                (gact_ty None ty fainv ~err:(low_dim_arg_err str.value)
                   (Modalcell.id2 (Ctx.mode ctx)))
            with
            | Error nosynth ->
                (* However, if the given term *doesn't* synthesize, we want to report the low-dimensional error, so we pass that diagnostic on. *)
                check_of_synth ~nosynth status ctx stm tm.loc ty
            | Ok ty_fainv ->
                (* A pure permutation shouldn't ever be locking, but we may as well keep this here for consistency.  *)
                let ctx = Ctx.maybe_lock ctx fa in
                let cx = check (Kinetic `Nolet) ctx x ty_fainv in
                realize status
                  (Term.Act (cx, fa, (sort_of_ty ctx (view_type ty "checking act"), `Other))))
        | Some _, None -> fatal (Nonsynthesizing "pure symmetry of placeholder")
        | None, _ -> (
            (* It can also check if it is *not* a permutation and the arity is positive, since then we can extract the needed type of its argument from the boundary of the type it is checking against. *)
            let (Full_tube tyargs) = get_tyargs ty "type of checking degeneracy" in
            match D.factor (TubeOf.inst tyargs) (dom_deg fa) with
            | None ->
                (* Again, in this case, if the term synthesizes, we want the error reported to be Unequal_synthesized_type.  So we fall back to synthesizing if the checking type doesn't symmetrize, reporting the low-dimensional error in case of a failure to synthesize. *)
                let nosynth =
                  diagnostic
                    ((low_dim_ty_err str.value).make ~got:(TubeOf.inst tyargs) ~needed:(dom_deg fa))
                in
                check_of_synth ~nosynth status ctx stm tm.loc ty
            | Some (Factor nk) -> (
                let (Plus mk) = D.plus (D.plus_right nk) in
                let fa = deg_plus fa mk nk in
                match section_of_deg fa with
                | None ->
                    (* If the arity is zero, we just give up and try to synthesize. *)
                    check_of_synth status ctx stm tm.loc ty
                | Some (Face (fs, fp)) -> (
                    match pface_of_sface fs with
                    | `Id _ ->
                        fatal (Anomaly "non-permutation degeneracy doesn't have a proper section")
                    | `Proper fs -> (
                        if not (Modal.Mode.allows_deg (Ctx.mode ctx) fa) then
                          fatal (Nonparametric_mode_degeneracy (str.value, Ctx.mode ctx));
                        let arg = TubeOf.find tyargs fs in
                        let sxty = arg.ty in
                        let xty =
                          gact_ty
                            ~err:(anomaly_dim_err "dimension confusion in checking degeneracy")
                            None sxty (deg_of_perm fp)
                            (Modalcell.id2 (Ctx.mode ctx)) in
                        let ctx = Ctx.maybe_lock ctx fa in
                        let cx, xloc =
                          match x with
                          | Some x -> (check (Kinetic `Nolet) ctx x xty, x.loc)
                          | None -> (readback_nf ctx arg, None) in
                        (* We also have to check that the rest of the output type is correct. *)
                        let ex = eval_term (Ctx.env ctx) cx in
                        let sty =
                          with_loc xloc @@ fun () ->
                          act_ty ex xty fa ~err:(low_dim_arg_err str.value)
                            (Modalcell.id2 (Ctx.mode ctx)) in
                        match subtype_of ctx sty ty with
                        | Ok () ->
                            realize status
                              (Term.Act
                                 (cx, fa, (sort_of_ty ctx (view_type ty "checking act"), `Other)))
                        | Error why ->
                            fatal
                              (Unequal_synthesized_type
                                 {
                                   got = PVal (ctx, sty);
                                   expected = PVal (ctx, ty);
                                   which = None;
                                   why;
                                 }))))))
    (* Similarly, an application can always synthesize, but can also check, as a non-dependent application, if enough domains are ascribed or arguments are synthesizing. *)
    | Synth (App _), _ -> (
        let fn, args = spine tm in
        let ctm, sty = synth_or_check_apps ctx fn args (Some ty) in
        (* We still have to check that the synthesized type is correct, as in check_of_synth. *)
        match subtype_of ctx sty ty with
        | Ok () -> realize status ctm
        | Error why ->
            fatal
              (Unequal_synthesized_type
                 { got = PVal (ctx, sty); expected = PVal (ctx, ty); which = None; why }))
    | Lam { name = { value = x; loc = xloc }; cube; implicit; dom; body }, _ -> (
        match view_type ~severity ty "typechecking lambda" with
        | Canonical
            ( _,
              Pi
                (type dom modality n)
                ({ x = _; filter; doms; cods } : (dom, modality, mode, n, _) pi_args),
              ins,
              tyargs ) -> (
            let modality = Modality.filter_modality filter in
            let Eq = eq_of_ins_zero ins in
            (* TODO: Move this into a helper function, it's too long to go in here. *)
            (* m is the outer (unfiltered) dimension of the pi-type; k is the filtered dimension at which the bound variables live. *)
            let m = BindCube.dim cods in
            let k = CubeOf.dim doms in
            (* If the domain was supplied, the lambda must be zero-dimensional, and the supplied domain must match the checking domain, including its modality, or at least contain it as a subtype (contravariance!). *)
            (match (dom, D.compare_zero m) with
            | Some _, Pos _ -> fatal (Unimplemented "domain-ascribed higher abstractions")
            | Some (dmod, dom), Zero -> (
                (match Modality.compare_name dmod.value modality with
                | Ok () -> ()
                | Error (`Unequal (Wrap m)) ->
                    fatal ?loc:dmod.loc ~severity:Asai.Diagnostic.Error
                      (Modality_mismatch (`User, "checking ascribed lambda", m, modality))
                | Error ((`Not_found _ | `Wrong_tgt _) as e) ->
                    modality_fatal "checking ascribed lambda" (e :> modality_error));
                let (Locked (_, lctx)) = Ctx.lock ctx modality in
                let cdom =
                  check (Kinetic `Nolet) lctx dom (universe (Modality.src modality) D.zero) in
                let edom = eval_term (Ctx.env lctx) cdom in
                match subtype_of lctx (CubeOf.find_top doms) edom with
                | Ok () -> ()
                | Error why ->
                    fatal ?loc:dom.loc
                      (Unequal_synthesized_type
                         {
                           got = PVal (lctx, edom);
                           expected = PVal (lctx, CubeOf.find_top doms);
                           which = None;
                           why;
                         }))
            | _ -> ());
            (* A zero-dimensional parameter that is a discrete type doesn't block discreteness, but others do. *)
            let discrete =
              match D.compare m D.zero with
              | Eq -> if is_discrete ?discrete (CubeOf.find_top doms) then discrete else None
              | Neq -> None in
            let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus m) in
            (* Extend the context by one variable for each type in doms, instantiated at the appropriate previous ones. *)
            let newargs, newnfs = dom_vars ctx modality doms in
            (* A helper function to update the status *)
            let mkstatus (xs : n variables) :
                (mode, b, s) status -> (mode, (b, (modality, n) dim_entry) snoc, s) status =
              function
              | Kinetic l -> Kinetic l
              | Potential (c, args, hyp) ->
                  let arg = CubeOf.mmap { map = (fun _ [ x ] -> Ctx.Binding.value x) } [ newnfs ] in
                  Potential
                    (c, Arg (args, filter, arg, ins_zero m), fun tm -> hyp (Lam (xs, m, filter, tm)))
            in
            (* Apply and instantiate the codomain to those arguments to get a type to check the body at. *)
            let output = tyof_app cods tyargs filter newargs in
            match cube.value with
            (* If the abstraction is not a cube, we slurp up the right number of lambdas for the dimension of the pi-type, requiring all but the top variable to be {implicit}, and pick up the body inside them.  We do this by building a cube of variables of the right dimension while maintaining the current term as an indexed state.  We also build a sum of raw lengths, since we need that to extend the context.  Note that we never need to manually "count" how many faces there are in a cube of any dimension, or discuss how to put them in order: the counting and ordering is handled automatically by iterating through a cube. *)
            | `Normal -> (
                let module S = struct
                  type 'b t =
                    | Ok : (a, 'b, 'ab) N.plus * 'ab check located -> 'b t
                    | Missing of int
                end in
                let module Build = NICubeOf.Traverse (S) in
                match
                  Build.build_left k
                    {
                      build =
                        (fun fa -> function
                          | Ok
                              ( ab,
                                {
                                  value =
                                    Lam
                                      {
                                        name;
                                        cube = { value = `Normal; _ };
                                        implicit;
                                        dom = _;
                                        body;
                                      };
                                  _;
                                } ) -> (
                              match (is_id_sface fa, implicit) with
                              | Some _, `Implicit ->
                                  fatal ?loc:name.loc
                                    (Unexpected_implicitness
                                       (`Implicit, "abstraction", "expecting explicit variable"))
                              | None, `Explicit ->
                                  fatal ?loc:name.loc
                                    (Unexpected_implicitness
                                       (`Explicit, "abstraction", "expecting implicit variable"))
                              | _ ->
                                  Fwrap
                                    ( NFamOf
                                        (View.hinted name.value
                                           (Ctx.Binding.value (CubeOf.find newnfs fa)).ty),
                                      Ok (Suc ab, body) ))
                          | Ok (_, _) -> Fwrap (NFamOf (`Anon no_hints), Missing 1)
                          | Missing j -> Fwrap (NFamOf (`Anon no_hints), Missing (j + 1)));
                    }
                    (Ok (Zero, tm))
                with
                | Wrap (names, Ok (af, body)) ->
                    let xs = Variables (D.zero, D.zero_plus k, names) in
                    let ctx =
                      Ctx.vis ctx
                        (Modality.filter_idempotent filter)
                        D.zero (D.zero_plus k) names newnfs af in
                    Lam (xs, m, filter, check ?discrete (mkstatus xs status) ctx body output)
                | Wrap (_, Missing j) -> fatal ?loc:cube.loc (Not_enough_lambdas j))
            | `Cube absdim -> (
                match (D.compare_zero m, implicit) with
                | Zero, _ -> fatal ?loc:cube.loc (Zero_dimensional_cube_abstraction "function")
                | _, `Implicit -> fatal (Unimplemented "general implicit functions")
                | Pos _, `Explicit ->
                    (match !absdim with
                    | None -> absdim := Some (Wrap m, xloc)
                    | Some (Wrap m', xloc') -> (
                        match D.compare m m' with
                        | Eq -> ()
                        | Neq ->
                            let extra_remarks =
                              Option.to_list
                                (Option.map
                                   (fun loc -> Asai.Diagnostic.loctext ~loc "previous variable")
                                   xloc') in
                            fatal ?loc:xloc ~extra_remarks
                              (Mismatched_dimensions_in_cube_abstraction (m', m))));
                    (* Here we don't need to slurp up lots of lambdas, but can make do with one. *)
                    let xs =
                      singleton_variables k
                        (View.hinted x (Ctx.Binding.value (CubeOf.find_top newnfs)).ty) in
                    let ctx = Ctx.cube_vis ctx (Modality.filter_idempotent filter) x newnfs in
                    Lam (xs, m, filter, check ?discrete (mkstatus xs status) ctx body output)))
        | _ -> fatal (Checking_lambda_at_nonfunction (PVal (ctx, ty))))
    | Struct (Noeta, tms), Potential _ -> (
        match view_type ~severity ty "typechecking comatch" with
        | Canonical (name, Codata ({ eta = Noeta; _ } as codata_args), ins, tyargs) ->
            let mn = is_id_ins ins <|> Comatching_at_degenerated_codata (phead name) in
            check_struct status Noeta ctx ty (cod_left_ins ins) mn codata_args tyargs tms
        | _ -> fatal (Comatching_at_noncodata (PVal (ctx, ty))))
    | Struct (Eta, tms), _ -> (
        match view_type ~severity ty "typechecking tuple" with
        | Canonical (name, Codata ({ eta = Eta; _ } as codata_args), ins, tyargs) ->
            let mn = is_id_ins ins <|> Checking_tuple_at_degenerated_record (phead name) in
            check_struct status Eta ctx ty (cod_left_ins ins) mn codata_args tyargs tms
        | _ -> fatal (Checking_tuple_at_nonrecord (PVal (ctx, ty))))
    | Constr ({ value = constr; loc = constr_loc }, args), _ -> (
        (* TODO: Move this into a helper function, it's too long to go in here. *)
        match view_type ~severity ty "typechecking constr" with
        | Canonical
            (type hmode mn m n)
            (( name,
               Data
                 {
                   dim;
                   indices = Filled ty_indices;
                   constrs;
                   discrete = _;
                   recursive = _;
                   tyfam = _;
                   hints = _;
                 },
               ins,
               tyargs ) :
              hmode head * _ * (mn, m, n) insertion * (D.zero, mn, mn, mode normal) TubeOf.t) -> (
            let Eq = eq_of_ins_zero ins in
            (* We don't need the *types* of the parameters or indices, which are stored in the type of the constant name.  The variable ty_indices (defined above) contains the *values* of the indices of this instance of the datatype, while tyargs (defined by view_type, above) contains the instantiation arguments of this instance of the datatype.  We check that the dimensions agree, and find our current constructor in the datatype definition. *)
            match Abwd.find_opt constr constrs with
            | None -> fatal ?loc:constr_loc (No_such_constructor (`Data (phead name), constr))
            | Some (Dataconstr { env; args = constr_arg_tys; indices = constr_indices }) ->
                (* To typecheck a higher-dimensional instance of our constructor constr at the datatype, all the instantiation arguments must also be applications of lower-dimensional versions of that same constructor.  We check this, and extract the arguments of those lower-dimensional constructors.  What we naturally have is a *tube of lists*, but what check_at_tel wants is a *vector of tubes*, one per telescope entry; we do the conversion with a multiple-output traversal, as in readback and equality. *)
                let lgth = Telescope.length constr_arg_tys in
                let (Conses (cs, bs)) = Tlist.Tlist.conses lgth in
                let tyarg_args =
                  TubeOf.Heter.vec_of_hgt cs
                  @@ TubeOf.pmap
                       {
                         map =
                           (fun (type k)
                             (fa : (k, D.zero, mn, mn) tface)
                             ([ tm ] : (k, (mode normal, Tlist.nil) Tlist.cons) CubeOf.Heter.hft)
                           ->
                             match view_term tm.tm with
                             | Constr (tmname, n, tmargs) ->
                                 if tmname = constr then
                                   match D.compare n (dom_tface fa) with
                                   | Eq ->
                                       let ys =
                                         Vec.of_list_length_map
                                           (fun (Value.Modal (xfilt, a)) : (_, _) modal_value ->
                                             Modal
                                               (Modality.filter_modality xfilt, CubeOf.find_top a))
                                           lgth tmargs
                                         <|> Anomaly "inst arg wrong num args in checking constr"
                                       in
                                       CubeOf.Heter.hft_of_vec cs ys
                                   | Neq ->
                                       fatal
                                         (Dimension_mismatch ("checking constr", n, dom_tface fa))
                                 else
                                   fatal
                                     (Missing_instantiation_constructor (constr, `Constr tmname))
                             | _ ->
                                 fatal
                                   (Missing_instantiation_constructor
                                      (constr, `Nonconstr (PNormal (ctx, tm)))));
                       }
                       [ tyargs ] bs in
                (* Now, for each argument of the constructor, we:
                   1. Evaluate the argument *type* of the constructor (which are assembled in the telescope constr_arg_tys) at the parameters (which are in the environment already) and the previous evaluated argument *values* (which get added to the environment as we go throurgh check_at_tel);
                   2. Instantiate the result at the corresponding arguments of the lower-dimensional versions of the constructor, from tyarg_args;
                   3. Check the coressponding argument *value*, supplied by the user, against this type;
                   4. Evaluate this argument value and add it to the environment, to substitute into the subsequent types, and also later to the indices. *)
                let env, newargs = check_at_tel constr ctx env args constr_arg_tys tyarg_args in
                (* Now we substitute all those evaluated arguments into the indices, to get the actual (higher-dimensional) indices of our constructor application. *)
                let constr_indices =
                  Vec.mmap
                    (fun [ ix ] ->
                      CubeOf.build dim
                        { build = (fun fa -> eval_term (act_env env (opt_op_of_sface fa)) ix) })
                    [ constr_indices ] in
                (* The last thing to do is check that these indices are equal to those of the type we are checking against.  (So a constructor application "checks against the parameters but synthesizes the indices" in some sense.)  I *think* it should suffice to check the top-dimensional ones, the lower-dimensional ones being automatic.  For now, we check all of them, raising an anomaly in case I was wrong about that.  *)
                Vec.miter
                  (fun [ t1s; t2s ] ->
                    CubeOf.miter
                      {
                        it =
                          (fun fa [ t1; t2 ] ->
                            match equal_at ctx t1 t2.tm t2.ty with
                            | Ok () -> ()
                            | Error err -> (
                                match is_id_sface fa with
                                | Some _ ->
                                    fatal
                                      (Unequal_indices
                                         ( PNormal (ctx, { tm = t1; ty = t2.ty }),
                                           PNormal (ctx, t2),
                                           err ))
                                | None ->
                                    fatal (Anomaly "mismatching lower-dimensional constructors")));
                      }
                      [ t1s; t2s ])
                  [ constr_indices; ty_indices ];
                realize status (Term.Constr (constr, dim, newargs)))
        (* A constructor can also check at a function-type by eta-expansion. *)
        | Canonical (_, Pi { x; _ }, _, _) ->
            let name = locate_opt None (option_of_binder_name (top_variable x)) in
            let cube, fa =
              match D.compare_zero (dim_variables x) with
              | Zero -> (locate_opt None `Normal, None)
              | Pos _ ->
                  (locate_opt None (`Cube (ref None)), Some (Any_sface (id_sface (dim_variables x))))
            in
            let args =
              List.fold_right
                (fun arg acc -> locate_opt arg.loc (Weaken (arg.value, Eq)) :: acc)
                args
                [ locate_opt None (Synth (Var (Top, fa))) ] in
            let body = locate_opt tm.loc (Constr ({ value = constr; loc = constr_loc }, args)) in
            check ?discrete status ctx
              (locate_opt tm.loc (Lam { name; cube; implicit = `Explicit; dom = None; body }))
              ty
        | _ -> fatal (No_such_constructor (`Other (PVal (ctx, ty)), constr)))
    | Numeral n, _ ->
        if n.num < Z.zero then fatal (Anomaly "negative numeral");
        if n.den <= Z.zero then fatal (Anomaly "negative denominator");
        (* A numeral is built out of 'suc', 'zero', and 'quot' (if it's a decimal) constructors, plus if we're checking an integer at a type that has a 'one' constructor we use that instead of 'suc. zero.' so that for instance 1/2 becomes quot. (suc. zero.) (suc. one.) with an ordinary notation binding of / to quot. .  This is the reason we don't do the expansion into constructors at the postprocessing step, so we can use the type information to decide whether to use 'one.' or 'suc. zero.'.  *)
        let use_one =
          match view_type ~severity ty "checking numeral" with
          | Canonical (_, Data { constrs; _ }, _, _) -> Abwd.mem (Constr.intern "one") constrs
          | _ -> false in
        (* TODO: It would be better not to hardcode the constructor names.  It might also be nice to represent numerals more efficiently in syntax, as I think Agda does, rather than insisting on expanding them out completely into constructors. *)
        let zero = { value = Constr.intern "zero"; loc = tm.loc } in
        let one = { value = Constr.intern "one"; loc = tm.loc } in
        let suc = { value = Constr.intern "suc"; loc = tm.loc } in
        let quot = { value = Constr.intern "quot"; loc = tm.loc } in
        let rec process_nat (n : Z.t) =
          if n = Z.zero then { value = Raw.Constr (zero, []); loc = tm.loc }
          else { value = Raw.Constr (suc, [ process_nat (Z.sub n Z.one) ]); loc = tm.loc } in
        let rec process_pos (n : Z.t) =
          if n = Z.one then { value = Raw.Constr (one, []); loc = tm.loc }
          else { value = Raw.Constr (suc, [ process_pos (Z.sub n Z.one) ]); loc = tm.loc } in
        let numeral =
          if n.den = Z.one then
            if use_one && n.num > Z.zero then process_pos n.num else process_nat n.num
          else { value = Raw.Constr (quot, [ process_nat n.num; process_pos n.den ]); loc = tm.loc }
        in
        check ?discrete status ctx numeral ty
    | Synth (Match { tm; window; sort = `Implicit; branches; refutables; highers }), Potential _ ->
        check_implicit_match status ctx tm window branches refutables highers ty
    | Synth (Match { tm; window; sort = `Nondep i; branches; refutables = _; highers }), Potential _
      ->
        let (Wrap window) = get_window (Ctx.mode ctx) window in
        let (Locked (plus_lock, lctx)) = Ctx.lock ctx window in
        let stm, sty = synth (Kinetic `Nolet) lctx tm in
        check_nondep_match status ctx stm sty window plus_lock branches (Some i) highers ty tm.loc
    (* We don't need to deal with `Explicit matches here, since they can always synthesize a type and hence be caught by the catch-all for checking synthesizing terms, below. *)
    (* Checking [] at a pi-type interprets it as a pattern-matching lambda over some empty datatype. *)
    | Empty_co_match, _ -> (
        match (view_type ~severity ty "checking empty (co)match", status) with
        | Canonical (_, Pi _, _, _), Potential _ -> check_empty_match_lam ctx ty `First
        | Canonical (_, Pi _, _, _), Kinetic l -> kinetic_of_potential l ctx tm ty "matching lambda"
        | _, _ -> check status ctx { value = Struct (Noeta, Abwd.empty); loc = tm.loc } ty)
    | Refute (tms, i), Potential _ -> check_refute status ctx tms ty i None
    (* Now we go through the canonical types. *)
    | Codata (fields, hints), Potential (head, apps, _) -> (
        match view_type ~severity ty "typechecking codata" with
        | Canonical (_, UU (_mode, dim), ins, tyargs) -> (
            match (D.compare_zero dim, Endpoints.hott (), !gel_ok) with
            | Pos _, Some _, false ->
                fatal (Unimplemented "general higher-dimensional types in HOTT: use glue")
            | _ ->
                let Eq = eq_of_ins_zero ins in
                let has_higher_fields =
                  Bwd.fold_left
                    (fun acc (Field.Wrap fld, _) ->
                      match acc with
                      | Some () -> Some ()
                      | None -> (
                          match D.compare (Field.dim fld) D.zero with
                          | Eq -> None
                          | Neq -> Some ()))
                    None fields in
                check_codata status ctx `Opaque Noeta hints tyargs Emp
                  (Fibrancy.Codata.empty dim dim (Ctx.tctx ctx) Noeta
                     (readback_neu ctx (head_of_potential head) apps))
                  (Bwd.to_list fields) Emp ~has_higher_fields)
        | _ -> fatal (Checking_canonical_at_nonuniverse ("codatatype", PVal (ctx, ty))))
    | SelfRecord (fields, opacity, hints), Potential (head, apps, _) -> (
        match view_type ~severity ty "typechecking self-record" with
        | Canonical (_, UU (_mode, dim), ins, tyargs) -> (
            match (D.compare_zero dim, Endpoints.hott (), !gel_ok) with
            | Pos _, Some _, false ->
                fatal (Unimplemented "general higher-dimensional types in HOTT: use glue")
            | _ -> (
                let Eq = eq_of_ins_zero ins in
                let has_higher_fields =
                  Bwd.fold_left
                    (fun acc (Field.Wrap fld, _) ->
                      match acc with
                      | Some () -> Some ()
                      | None -> (
                          match D.compare (Field.dim fld) D.zero with
                          | Eq -> None
                          | Neq -> Some ()))
                    None fields in
                match has_higher_fields with
                | Some () -> fatal (Unimplemented "higher fields in record types: use codata")
                | None ->
                    check_codata status ctx opacity Eta hints tyargs Emp
                      (Fibrancy.Codata.empty dim dim (Ctx.tctx ctx) Eta
                         (readback_neu ctx (head_of_potential head) apps))
                      (Bwd.to_list fields) Emp ~has_higher_fields))
        | _ -> fatal (Checking_canonical_at_nonuniverse ("codatatype", PVal (ctx, ty))))
    | Record (xs, fields, opacity, hints), Potential (head, apps, _) -> (
        match view_type ~severity ty "typechecking record" with
        | Canonical (_, UU (_mode, dim), ins, tyargs) -> (
            match (D.compare_zero dim, Endpoints.hott (), !gel_ok) with
            | Pos _, Some _, false ->
                fatal (Unimplemented "general higher-dimensional types in HOTT: use glue")
            | _ ->
                let Eq = eq_of_ins_zero ins in
                let (Vars (af, vars)) = vars_of_names xs.loc dim xs.value in
                check_record status dim ctx opacity hints tyargs vars Emp Zero af Emp
                  (Fibrancy.Codata.empty dim dim (Ctx.tctx ctx) Eta
                     (readback_neu ctx (head_of_potential head) apps))
                  fields Emp)
        | _ -> fatal (Checking_canonical_at_nonuniverse ("record type", PVal (ctx, ty))))
    | Data (constrs, hints), Potential _ ->
        (* For a datatype, the type to check against might not be a universe, it could include indices.  We also check whether all the types of all the indices are discrete or a type being defined, to decide whether to keep evaluating the type for discreteness. *)
        let n, disc = typefam ?discrete ctx ty in
        let (Wrap num_indices) = Fwn.of_int n in
        check_data
          ~discrete:(if disc then discrete else None)
          ~recursive:`Nonrecursive ~hints status ctx ty num_indices Abwd.empty (Bwd.to_list constrs)
          Emp
    (* If we have a term that's not valid outside a case tree, we bind it to a global metavariable. *)
    | Struct (Noeta, _), Kinetic l -> kinetic_of_potential l ctx tm ty "comatch"
    | Synth (Match _), Kinetic l -> kinetic_of_potential l ctx tm ty "match"
    | Refute _, Kinetic l -> kinetic_of_potential l ctx tm ty "match"
    | Codata _, Kinetic l -> kinetic_of_potential l ctx tm ty "codata"
    | SelfRecord _, Kinetic l -> kinetic_of_potential l ctx tm ty "sig"
    | Record _, Kinetic l -> kinetic_of_potential l ctx tm ty "sig"
    | Data _, Kinetic l -> kinetic_of_potential l ctx tm ty "data"
    (* If the user left a hole, we create an eternal metavariable. *)
    | Hole { scope = vars; loc = pos; li; ri; num }, _ ->
        (* Holes aren't numbered by the file they appear in. *)
        let meta =
          Meta.make_hole (Ctx.mode ctx) (Ctx.raw_length ctx) (Ctx.tctx ctx) (energy status) in
        num := Meta.hole_number meta;
        let ty, termctx =
          Readback.Displaying.run ~env:true @@ fun () -> (readback_val ctx ty, readback_ctx ctx)
        in
        Global.add_hole meta pos ~vars ~termctx ~ty ~status ~li ~ri;
        (* The hole might be solved later with a term containing occurrences of currently-being-defined constants, so we record it as blocking any enclosing occurrence-analysis scope. *)
        Positivity.record_hole meta;
        Meta (meta, energy status)
    (* If we have a synthesizing term, we synthesize it. *)
    | Synth stm, _ -> check_of_synth status ctx stm tm.loc ty
    (* We pass through case tree leaf markers *)
    | Realize ktm, Potential _ -> Realize (check (Kinetic `Nolet) ctx (locate_opt tm.loc ktm) ty)
    | Realize ktm, Kinetic l -> check (Kinetic l) ctx (locate_opt tm.loc ktm) ty
    (* Nothing is embedded *)
    | Embed _, _ -> .
    (* If we're using the checking type as an implicit first argument: *)
    | ImplicitApp (fn, args), _ -> (
        (* We read it back, so we can put it as the first argument in the generated term. *)
        let cty = readback_val ctx ty in
        (* Now we act like synth on an application. *)
        let sfn, sty = synth (Kinetic `Nolet) ctx fn in
        match view_type sty "ImplicitApp" with
        | Canonical (_, Pi { x = _; filter; doms; cods }, ins, tyargs) -> (
            let Eq = eq_of_ins_zero ins in
            let modality = Modality.filter_modality filter in
            (* Only 0-dimensional and non-modal applications are allowed. *)
            match (D.compare (CubeOf.dim doms) D.zero, Modality.compare_id modality) with
            | Eq, Eq -> (
                (* The first argument must be a type. *)
                match view_type (CubeOf.find_top doms) "ImplicitApp argument" with
                | Canonical (_, UU _, _, _) -> (
                    (* We build the implicit application term and its type. *)
                    let mode = Ctx.mode ctx in
                    let idm = Modality.id mode in
                    let new_sfn =
                      locate_opt fn.loc
                        (Term.App
                           ( sfn,
                             D.zero,
                             Modality.filter_id mode D.zero,
                             Modal (idm, plus_no_lock mode, CubeOf.singleton cty) )) in
                    let new_sty = tyof_app cods tyargs filter (CubeOf.singleton ty) in
                    (* And then proceed applying to the rest of the arguments, if any. *)
                    let stm, sty =
                      match args with
                      | _ :: _ ->
                          let args =
                            List.map
                              (fun (l, x) ->
                                (l, { value = Some x.value; loc = x.loc }, locate_opt None `Explicit))
                              args in
                          synth_apps ctx new_sfn new_sty
                            { value = Synth fn.value; loc = fn.loc }
                            args
                      | _ -> (new_sfn.value, new_sty) in
                    (* Then we have to check that the resulting type of the whole application agrees with the one we're checking against. *)
                    match equal_val ctx sty ty with
                    | Ok () -> realize status stm
                    | Error why ->
                        fatal
                          (Unequal_synthesized_type
                             { got = PVal (ctx, sty); expected = PVal (ctx, ty); which = None; why })
                    )
                | _ ->
                    fatal ?loc:fn.loc
                      (Anomaly "first argument of an ImplicitMap is not of type Type"))
            | Neq, _ ->
                fatal ?loc:fn.loc (Dimension_mismatch ("ImplicitApp", CubeOf.dim doms, D.zero))
            | _, Neq -> fatal ?loc:fn.loc (Anomaly "modal implicit applications not allowed"))
        | _ -> fatal ?loc:fn.loc (Applying_nonfunction_nontype (PTerm (ctx, sfn), PVal (ctx, sty))))
    | First alts, _ ->
        let rec go errs = function
          | [] -> fatal (Choice_mismatch (PVal (ctx, ty)))
          | (test, alt, passthru) :: alts -> (
              match (view_type ty "check_first", test) with
              | Canonical (_, Data { constrs = data_constrs; _ }, _, _), `Data constrs ->
                  if
                    List.for_all
                      (fun constr ->
                        Bwd.exists (fun (data_constr, _) -> constr = data_constr) data_constrs)
                      constrs
                  then
                    Reporter.try_with ~fatal:(fun d ->
                        if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                    @@ fun () -> check ?discrete status ctx (locate_opt tm.loc alt) ty
                  else go errs alts
              | Canonical (_, Codata { fields = codata_fields; _ }, _, _), `Codata fields ->
                  if
                    List.for_all
                      (fun field ->
                        Bwd.exists
                          (fun (CodatafieldAbwd.Entry (codata_field, _)) ->
                            field = Field.to_string codata_field)
                          codata_fields)
                      fields
                  then
                    Reporter.try_with ~fatal:(fun d ->
                        if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                    @@ fun () -> check ?discrete status ctx (locate_opt tm.loc alt) ty
                  else go errs alts
              | _, `Any ->
                  Reporter.try_with ~fatal:(fun d ->
                      if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                  @@ fun () -> check ?discrete status ctx (locate_opt tm.loc alt) ty
              | _ -> go errs alts) in
        go Emp alts
    | Oracle tm, _ -> (
        let ctm = check (Kinetic `Nolet) ctx tm ty in
        let etm = eval_term (Ctx.env ctx) ctm in
        match Oracle.ask (Ask (ctx, etm)) with
        | Ok () -> (
            (* TODO: try just "realize ctm" *)
            match status with
            | Kinetic _ -> ctm
            | Potential _ -> Realize ctm)
        | Error err -> fatal err)
    | Weaken (body, Eq), _ -> (
        match Ctx.pop ctx with
        | Ok (Pop (ctx, Eq, Eq)) ->
            Weaken (check ?discrete (pop_status status) ctx (locate_opt tm.loc body) ty)
        | Error e -> fatal (Anomaly ("failed to weaken raw term: " ^ e))) in
  with_loc tm.loc @@ fun () ->
  Annotate.ctx status ctx tm;
  Annotate.ty ctx ty;
  let result = go () in
  Annotate.tm ctx result;
  result

(* Deal with a synthesizing term in checking position. *)
and check_of_synth : type mode a b s.
    ?nosynth:Code.t Asai.Diagnostic.t ->
    (mode, b, s) status ->
    (mode, a, b) Ctx.t ->
    a synth ->
    Asai.Range.t option ->
    (mode, kinetic) value ->
    (mode, b, s) term =
 fun ?nosynth status ctx stm loc ty ->
  match stm with
  | Asc (ctm, aty) -> (
      (* If the term is synthesizing because it is ascribed, then we can accumulate errors: if the ascription fails to check, or if it fails to equal the checking type, we can proceed to check the ascribed term against the supplied type instead.  This will rarely happen in normal use, since there is no need to ascribe a term that's in checking position, but it can occur with some alternative frontends. *)
      Reporter.try_with ~fatal:(fun d1 ->
          Reporter.try_with ~fatal:(fun d2 ->
              fatal (Accumulated ("check_of_synth", Snoc (Snoc (Emp, d1), d2))))
          @@ fun () ->
          let _ = check status ctx ctm ty in
          fatal_diagnostic d1)
      @@ fun () ->
      let cty = check (Kinetic `Nolet) ctx aty (universe (Ctx.mode ctx) D.zero) in
      let ety = eval_term (Ctx.env ctx) cty in
      (* It suffices for the synthesized type to be a subtype of the checking type. *)
      match subtype_of ctx ety ty with
      | Ok () -> check status ctx ctm ety
      | Error why ->
          fatal
            (Unequal_synthesized_type
               { got = PVal (ctx, ety); expected = PVal (ctx, ty); which = None; why }))
  | _ -> (
      let sval, sty = synth ?nosynth status ctx { value = stm; loc } in
      (* It suffices for the synthesized type to be a subtype of the checking type. *)
      match subtype_of ctx sty ty with
      | Ok () -> sval
      | Error why ->
          fatal
            (Unequal_synthesized_type
               { got = PVal (ctx, sty); expected = PVal (ctx, ty); which = None; why }))

(* Deal with checking a potential term in kinetic position *)
and kinetic_of_potential : type mode a b.
    [ `Let | `Nolet ] ->
    (mode, a, b) Ctx.t ->
    a check located ->
    (mode, kinetic) value ->
    string ->
    (mode, b, kinetic) term =
 fun l ctx tm ty sort ->
  match l with
  | `Let -> raise Case_tree_construct_in_let
  | `Nolet ->
      emit (Bare_case_tree_construct sort);
      (* We create a metavariable to store the potential value. *)
      let meta =
        Meta.make_def sort None (Ctx.mode ctx) (Ctx.raw_length ctx) (Ctx.tctx ctx) Potential in
      (* We first define the metavariable without a value, as an "axiom", just as we do for global constants.  This isn't necessary for recursion, since this metavariable can't refer to itself, but so that with_meta_definition will be able to find it for consistency. *)
      let termctx = readback_ctx ctx in
      let vty = readback_val ctx ty in
      Global.add_meta meta ~termctx ~tm:`Axiom ~ty:vty ~energy:Potential;
      (* Then we check the value and redefine the metavariable to be that value. *)
      let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, fun x -> x) in
      let cv = check tmstatus ctx tm ty in
      Global.set_meta meta cv;
      (* Finally, we return the metavariable. *)
      Term.Meta (meta, Kinetic)

and synth_or_check_let : type mode a b s p.
    ?nosynth:Code.t Asai.Diagnostic.t ->
    (mode, b, s) status ->
    (mode, a, b) Ctx.t ->
    string option ->
    string located list located ->
    a synth located ->
    a N.suc check located ->
    ((mode, kinetic) value, p) Perhaps.t ->
    (mode, b, s) term * ((mode, kinetic) value, p) Perhaps.not =
 fun ?nosynth status ctx name premod v body ty ->
  (* A non-recursive let-binding can be modal. *)
  match Modality.of_name_tgt (Ctx.mode ctx) premod.value with
  | Error e -> modality_fatal "checking let-in" (e :> modality_error)
  | Ok (Wrap (type dom modality) (modality : (dom, modality, mode) Modality.t)) -> (
      let (Locked (plus, lctx)) = Ctx.lock ctx modality in
      (* The bound value is checked in an occurrence-analysis scope, and the resulting verdict is stored as the "dirt" of the new variable's binding, so that references to the variable from datatype constructor types can detect occurrences of currently-being-defined constants hiding in its value. *)
      let (v, nf), dirt =
        Positivity.scope @@ fun () ->
        try
          (* We first try checking the bound term first as an ordinary kinetic term. *)
          let sv, svty = synth (Kinetic `Let) lctx v in
          let ev = eval_term (Ctx.env lctx) sv in
          (sv, { tm = ev; ty = svty })
        with
        (* If that encounters case-tree constructs, then we can allow the bound term to be a case tree, i.e. a potential term.  But in a checked "let" expression, the term being bound is a kinetic one, and must be so that its value can be put into the environment when the term is evaluated.  We deal with this by binding a *metavariable* to the bound term and then taking the value of that metavariable as the kinetic term to actually be bound.  *)
        | Case_tree_construct_in_let ->
          (* First we make the metavariable. *)
          let meta =
            Meta.make_def "let" name (Ctx.mode lctx) (Ctx.raw_length lctx) (Ctx.tctx lctx) Potential
          in
          let termctx = readback_ctx lctx in
          (* A new status in which to check the value of that metavariable; now it is the "current constant" being defined. *)
          let tmstatus = Potential (Meta (meta, Ctx.env lctx), Emp, fun x -> x) in
          let sv, svty =
            match v.value with
            | Asc (vtm, rvty) ->
                (* If the bound term is explicitly ascribed, then we can give the metavariable a type while checking its body.  This is probably mainly only useful with "let rec". *)
                let vty = check (Kinetic `Nolet) lctx rvty (universe (Ctx.mode lctx) D.zero) in
                Global.add_meta meta ~termctx ~tm:`Axiom ~ty:vty ~energy:Potential;
                let evty = eval_term (Ctx.env lctx) vty in
                let cv = check tmstatus lctx vtm evty in
                Global.set_meta meta cv;
                (cv, evty)
            | _ ->
                (* Otherwise, we just synthesize the term. *)
                let sv, svty = synth tmstatus lctx v in
                let vty = readback_val lctx svty in
                Global.add_meta meta ~termctx ~tm:(`Defined sv) ~ty:vty ~energy:Potential;
                (sv, svty) in
          (* We turn that metavariable into a value. *)
          let head = Value.Meta { meta; env = Ctx.env lctx; ins = zero_ins D.zero } in
          let tm =
            if GluedEval.read () then
              (* Glued evaluation: we delay evaluating the term until it's needed. *)
              Neu { head; args = Emp; value = lazy_eval (Ctx.env lctx) sv; ty = Lazy.from_val svty }
            else
              match eval (Ctx.env lctx) sv with
              | Realize x -> x
              | value -> Neu { head; args = Emp; value = ready value; ty = Lazy.from_val svty }
          in
          (Term.Meta (meta, Kinetic), { tm; ty = svty }) in
      (* Either way, we end up with a checked term 'v' and a normal form 'nf'.  We use the latter to extend the context. *)
      let newctx = Ctx.ext_let ~dirt ctx modality name nf in
      (* Now we update the status of the original constant being checked *)
      let status : (mode, (b, (modality, D.zero) dim_entry) snoc, s) status =
        match status with
        | Potential (c, args, hyp) ->
            Potential (c, args, fun body -> hyp (Let (name, Modal (modality, plus, v), body)))
        | Kinetic l -> Kinetic l in
      (* And synthesize or check the body in the extended context. *)
      Annotate.ctx status newctx body;
      match (ty, body) with
      | Some ty, _ ->
          let sbody = check status newctx body ty in
          (Term.Let (name, Modal (modality, plus, v), sbody), Not_some)
      | None, { value = Synth body; loc } ->
          let sbody, sbodyty = synth status newctx { value = body; loc } in
          (Term.Let (name, Modal (modality, plus, v), sbody), Not_none sbodyty)
      | None, _ -> fatal_or nosynth (Nonsynthesizing "let-expression without synthesizing body"))

and synth_or_check_letrec : type mode a b c ac s p.
    ?nosynth:Code.t Asai.Diagnostic.t ->
    (mode, b, s) status ->
    (mode, a, b) Ctx.t ->
    (a, c, ac) Raw.tel ->
    (ac check located, c) Vec.t ->
    ac check located ->
    ((mode, kinetic) value, p) Perhaps.t ->
    (mode, b, s) term * ((mode, kinetic) value, p) Perhaps.not =
 fun ?nosynth status ctx rvtys vtms body ty ->
  let mode = Ctx.mode ctx in
  (* First we check the types of all the bound variables, which are a telescope since each can depend on the previous ones. *)
  let Checked_tel (type bc) ((vtys, _) : (mode, _, _, bc) Telescope.t * (_, _, bc) Ctx.t), _ =
    check_tel ctx rvtys in
  (* Then we create the metavariables. *)
  let metas = make_letrec_metas ctx vtys in
  (* Now we check the bound terms. *)
  let ac = Raw.bplus_of_tel rvtys in
  let () = check_letrec_bindings mode ctx ac metas vtys vtms in
  (* Now we update the status of the original constant being checked *)
  let status : (mode, bc, s) status =
    match status with
    | Potential (c, args, hyp) -> Potential (c, args, fun x -> hyp (let_metas mode metas x))
    | Kinetic l -> Kinetic l in
  (* Make a context for it *)
  let _, newctx = ext_metas ctx ac metas vtys Zero Zero Zero in
  (* And synthesize or check the body in the extended context. *)
  Annotate.ctx status newctx body;
  match (ty, body) with
  | Some ty, _ ->
      let sbody = check status newctx body ty in
      (let_metas mode metas sbody, Not_some)
  | None, { value = Synth body; loc } ->
      let sbody, sbodyty = synth status newctx { value = body; loc } in
      (let_metas mode metas sbody, Not_none sbodyty)
  | None, _ -> fatal_or nosynth (Nonsynthesizing "let-expression without synthesizing body")

and check_letrec_bindings : type mode a xc b ac bc.
    mode Modal.Mode.t ->
    (mode, a, b) Ctx.t ->
    (a, xc, ac) Fwn.bplus ->
    (mode, b, xc, bc) meta_tel ->
    (mode, b, xc, bc) Telescope.t ->
    (ac check located, xc) Vec.t ->
    unit =
 fun mode octx oac ometas ovtys vs ->
  (* A let-rec is NOT allowed to be modal.  I had technical problems with context manipulation in trying to figure out how to check a modal letrec, plus I'm not even sure what that would mean semantically. *)
  let rec go : type x ax bx c.
      (a, x, ax) Fwn.bplus ->
      (x, c, xc) Fwn.plus ->
      (b, x, (mode id, D.zero) dim_entry, bx) Tbwd.snocs ->
      (* *)
      (ax, c, ac) Fwn.bplus ->
      (mode, bx, c, bc) meta_tel ->
      (mode, bx, c, bc) Telescope.t ->
      (ac check located, c) Vec.t ->
      unit =
   fun ax xc bx ac metas vtys vs ->
    match (ac, metas, vtys, vs) with
    | Zero, Nil, Emp, [] -> ()
    | Suc ac, Ext (_, meta, metas), Ext (name, Modal (modality, plus, vty), vtys), v :: vs -> (
        match (Modality.compare_id modality, plus) with
        | Eq, Plus_lock (Zero _, Zero) ->
            let ctx, tmctx = ext_metas octx oac ometas ovtys ax xc bx in
            let evty = eval_term (Ctx.env ctx) vty in
            (* This use of let_metas is sneaky.  All the defined metavariables have to depend on each other mutually, but in the *context* each bound variable can only depend on those to its left.  So we make it "depend" on the other variables by wrapping it in a let-binding that sets those textual variables to the correct metavariables.  This is also why we don't know how to do modal let-recs: if the let-rec variables are at different model or modalities, it's unclear how one of them could be wrapped in let-bindings of the others.  *)
            let hyp b =
              Term.Let (name, Modal (modality, plus, Meta (meta, Kinetic)), let_metas mode metas b)
            in
            let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, hyp) in
            (* The bound value is checked in an occurrence-analysis scope, and the verdict is recorded on the metavariable, whence ext_metas reads it as the "dirt" of the corresponding context variable.  (While this value is being checked, the metavariables of it and its mutual companions are still undefined in Global, so ext_metas marks all the variables of tmctx as dirty; thus self- and companion-references count as recursive occurrences.) *)
            let cv, recursion = Positivity.scope @@ fun () -> check tmstatus tmctx v evty in
            Global.set_meta meta ~recursion (hyp cv);
            (* And recurse. *)
            go (Fwn.bplus_suc_eq_suc ax) (Fwn.suc_plus xc) (Tbwd.snocs_suc_eq_snoc bx) ac metas vtys
              vs
        | _ -> fatal (Unimplemented "modal let-rec variables")) in
  go Zero Zero Zero oac ometas ovtys vs

(* Given a telescope of types for let-bound variables, create a global metavariable for each of them, and give it the correct type in Global. *)
and make_letrec_metas : type mode x a b ab.
    (mode, x, a) Ctx.t -> (mode, a, b, ab) Telescope.t -> (mode, a, b, ab) meta_tel =
 fun ctx tel ->
  match tel with
  | Emp -> Nil
  | Term.Ext (x, Modal (modality, plus, vty), tel) -> (
      match (Modality.compare_id modality, plus) with
      | Eq, Plus_lock (Zero _, Zero) ->
          (* Create the metavariable. *)
          let meta =
            Meta.make_def "letrec" x (Ctx.mode ctx) (Ctx.raw_length ctx) (Ctx.tctx ctx) Potential
          in
          (* Assign it the correct type. *)
          let termctx = readback_ctx ctx in
          Global.add_meta meta ~termctx ~tm:`Axiom ~ty:vty ~energy:Potential;
          (* Extend the context by it, as an unrealized neutral.  TODO: It's annoying that we have to evaluate the types here to extend the value-context, when the only use we're making of it is to readback that extended value-context into a termctx at each step to save with the global metavariable.  It would make more sense, and be more efficient, to just carry along the termctx and extend it directly at each step with "Term.Meta (meta, Kinetic)" at the term-type "vty".  Unfortunately, termctxs store terms and types in a one-longer context, so that would require directly weakening vty, or perhaps parsing and checking it in a one-longer context originally. *)
          let evty = eval_term (Ctx.env ctx) vty in
          let head = Value.Meta { meta; env = Ctx.env ctx; ins = zero_ins D.zero } in
          let neutm = Neu { head; args = Emp; value = ready Unrealized; ty = Lazy.from_val evty } in
          let ctx = Ctx.ext_let ~dirt:(dirt_of_meta meta) ctx modality x { tm = neutm; ty = evty } in
          (* And recurse. *)
          Ext (x, meta, make_letrec_metas ctx tel)
      | _ -> fatal (Unimplemented "modal let-rec variables"))

and let_metas : type mode b c bc s.
    mode Modal.Mode.t -> (mode, b, c, bc) meta_tel -> (mode, bc, s) term -> (mode, b, s) term =
 fun mode metas tm ->
  match metas with
  | Nil -> tm
  | Ext (x, m, metas) ->
      Let
        (x, Modal (Modality.id mode, plus_no_lock mode, Meta (m, Kinetic)), let_metas mode metas tm)

(* The "dirt" of a context variable bound to a let-rec metavariable: if the metavariable is still undefined, it is currently being defined, so a reference to it is a recursive occurrence; once it is defined, we use the recursion verdict that was recorded when its value was checked. *)
and dirt_of_meta : type mode x a s. (mode, x, a, s) Meta.t -> Positivity.recursion =
 fun meta ->
  let df = Global.find_meta meta in
  match df.tm with
  | `Defined _ -> df.recursion
  | `Axiom | `Undefined -> `Recursive

(* Extend a context by evaluated metavariables to be used for let-rec.  We return both the fully extended context and a partially extended one. *)
and ext_metas : type mode a b c ac bc d cd acd bcd.
    (mode, a, b) Ctx.t ->
    (a, cd, acd) Fwn.bplus ->
    (mode, b, cd, bcd) meta_tel ->
    (mode, b, cd, bcd) Telescope.t ->
    (a, c, ac) Fwn.bplus ->
    (c, d, cd) Fwn.plus ->
    (b, c, (mode id, D.zero) dim_entry, bc) Tbwd.snocs ->
    (mode, ac, bc) Ctx.t * (mode, acd, bcd) Ctx.t =
 fun ctx acd metas vtys ac cd bc ->
  (* First we define a helper function that returns only the fully extended context. *)
  let rec ext_metas' : type a b cd acd bcd.
      (mode, a, b) Ctx.t ->
      (a, cd, acd) Fwn.bplus ->
      (mode, b, cd, bcd) meta_tel ->
      (mode, b, cd, bcd) Telescope.t ->
      (mode, acd, bcd) Ctx.t =
   fun ctx acd metas vtys ->
    match (acd, metas, vtys) with
    | Zero, Nil, Emp -> ctx
    | Suc acd, Ext (_, meta, metas), Ext (x, Modal (modality, plus, vty), vtys) -> (
        match (Modality.compare_id modality, plus) with
        | Eq, Plus_lock (Zero _, Zero) ->
            let tm = eval_term (Ctx.env ctx) (Meta (meta, Kinetic)) in
            let ty = eval_term (Ctx.env ctx) vty in
            ext_metas'
              (Ctx.ext_let ~dirt:(dirt_of_meta meta) ctx modality x { tm; ty })
              acd metas vtys
        | _ -> fatal (Unimplemented "modal let-rec variables")) in
  match (ac, cd, bc, acd, metas, vtys) with
  | Zero, Zero, Zero, _, _, _ -> (ctx, ext_metas' ctx acd metas vtys)
  | Suc ac, Suc cd, Suc bc, Suc acd, Ext (_, meta, metas), Ext (x, Modal (modality, plus, vty), vtys)
    -> (
      match (Modality.compare_id modality, plus) with
      | Eq, Plus_lock (Zero _, Zero) ->
          let tm = eval_term (Ctx.env ctx) (Meta (meta, Kinetic)) in
          let ty = eval_term (Ctx.env ctx) vty in
          ext_metas
            (Ctx.ext_let ~dirt:(dirt_of_meta meta) ctx modality x { tm; ty })
            acd metas vtys ac cd bc
      | _ -> fatal (Unimplemented "modal let-rec variables"))

(* Check a match statement without an explicit motive supplied by the user.  This means if the discriminee is a well-behaved variable, it can be a variable match; otherwise it reverts back to a non-dependent match. *)
and check_implicit_match : type mode a b.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    a synth located ->
    string located list located option ->
    (Constr.t, a branch) Abwd.t ->
    a refutables option ->
    bool ref located list ->
    (mode, kinetic) value ->
    (mode, b, potential) term =
 fun status ctx tm window_name brs refutables highers motive ->
  (* If the discriminee isn't a variable at all, we will pass off to checking a nondependent match using this function. *)
  let fallback () =
    let (Wrap window) = get_window (Ctx.mode ctx) window_name in
    let (Locked (plus, wctx)) = Ctx.lock ctx window in
    let stm, varty = synth (Kinetic `Nolet) wctx tm in
    check_nondep_match status ctx stm varty window plus brs None highers motive tm.loc in
  (* We look up the discriminee to check whether it is an unlocked free variable and get its De Bruijn level, its type, and its checked-index. *)
  match tm with
  | { value = Var ix; loc } -> (
      (* If it is locked, invalidly modally annotated, a field-access variable, or let-bound, we will also fall back to a nondependent match, but with a hint message since the user may have been expecting a variable match. *)
      let fallback reason arg =
        emit ?loc (Matching_wont_refine (reason, Some arg));
        fallback () in
      let (Lookup { result; value = { tm = _; ty = varty }; dirt; modality; filter; insert; plus })
          =
        Ctx.lookup ctx ix in
      (* This is a use of the variable, so we record its dirt for any active occurrence-analysis scope. *)
      Positivity.record dirt;
      let (Plus_with_locks (comp, locks)) = plus in
      let lock = Locks.cod locks in
      (* For a variable match, the variable cannot be locked. *)
      match (comp, locks) with
      | Suc _, Suc _ -> fallback "discriminee is locked" (PModality lock)
      | Zero, Zero _ -> (
          (* The modal annotation on the variable must match the window modality *if* that was given. *)
          (match window_name with
          | None -> ()
          | Some w -> (
              match Modality.of_name_tgt (Ctx.mode ctx) w.value with
              | Error e -> modality_fatal "checking let-in" (e :> modality_error)
              | Ok (Wrap window) -> (
                  match Modality.compare window modality with
                  | Eq -> ()
                  | Neq ->
                      fatal (Modality_mismatch (`User, "checking implicit match", window, modality))
                  )));
          let (Locked (plus, lctx)) = Ctx.lock ctx modality in
          let iplus = plus_with_locks_of_plus_lock plus in
          (* For a variable match, the variable must not be let-bound to a value or be a field access variable. *)
          match result with
          | `Field (_, field) -> fallback "discriminee is record field" (PField field)
          | `Var (None, fa) ->
              fallback "discriminee is let-bound"
                (PTerm (lctx, Var (Index (insert, fa, filter, iplus))))
          | `Var (Some level, fa) ->
              (* In this case we do have a valid variable match. *)
              let index = Index (insert, fa, filter, iplus) in
              with_loc loc (fun () ->
                  Annotate.ctx status ctx (locate_opt loc (Synth (Var ix)));
                  Annotate.ty lctx varty;
                  Annotate.tm lctx (Term.Var index));
              check_var_match status ctx level index varty modality plus brs refutables highers
                motive loc))
  | _ -> fallback ()

(* This subroutine iterates through the branches of a non-refining match, checking them all in an appropriate context against the same motive.  Since a non-dependent match might be either checking or synthesizing, the motive can be obtained in two ways, either supplied by the caller directly, or deduced from a branch whose body synthesizes.  We abstract away from this variation by having the caller of this subroutine supply a callback (of type match_motive) that computes a motive from the list of merged branches (see merge_branches).  Since in the process it might also try synthesizing one or more of the branches, it has to also return a list of errors, a list of already-typechecked branches, and the list of branches remaining to check.  Moreover, in the case of a dependent match when the *user* has specified a dependent motive, that motive has to be specialized differently in each branch; we abstract away from that by having the callback return an abstract type which another callback can specialize in each branch. *)
and check_match_branches : type dom window mode a b bm.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    (dom, bm, kinetic) term ->
    (dom, kinetic) value ->
    (dom, window, mode) Modality.t ->
    (b, mode, window, dom, bm) plus_lock ->
    (Constr.t, a branch) Abwd.t ->
    int located option ->
    bool ref located list ->
    Asai.Range.t option ->
    (dom, window, mode, a, b) match_motive ->
    (mode, b, potential) term * (mode, kinetic) value option =
 fun status ctx tm varty window plus_lock brs i highers loc (Motive callbacks) ->
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  match view_type varty "check_match_branches" with
  | Canonical
    (* Data always has intrinsic dimension zero, but it seems that the syntax for binding type variables in a GADT match can't take that into account.  So we have to give "zero" a name here, and two different names for m. *)
      (type hmode d_zero m m')
      (( name,
         Data
           (type j ij)
           ({
              dim;
              indices = Filled indices;
              constrs = data_constrs;
              tyfam;
              discrete = _;
              recursive;
              hints = _;
            } :
             (_, _, j, ij) data_args),
         ins,
         inst_args ) :
        hmode head
        * (dom, m, d_zero) canonical
        * (m', m, d_zero) insertion
        * (D.zero, m', m', dom normal) TubeOf.t) -> (
      (* But we can immediately identify the two different m's. *)
      let Eq = eq_of_ins_zero ins in
      check_window_transparency window data_constrs recursive;
      (* The argument 'i' counts the *number* of arguments to a motive in a match that was made explicitly non-dependent as in "match x return _ _ ↦ _".  In this case, we really don't care *what* the instantiation arguments are, and we really don't care what the indices are either except to check there are the right number of them.  This is because in the non-dependent case, we are just applying a recursor to a value, so we don't need to know that the indices and instantiation arguments are variables; in the branches they will be whatever they will be, but we don't even need to *know* what they will be because the output type isn't getting refined either. *)
      (match i with
      | Some { value; loc } ->
          (* +1 for the argument belonging to the datatype itself *)
          let needed = Fwn.to_int (Vec.length indices) + 1 in
          if value <> needed then fatal ?loc (Wrong_number_of_arguments_to_motive needed)
      | None -> ());
      (* We start with a preprocesssing step that pairs each user-provided branch with the corresponding constructor information from the datatype. *)
      let user_branches = merge_branches name brs data_constrs in
      (* We use the callback to get the motive and other data.  This might typecheck some of the branches, if it is a synthesizing match. *)
      let motive, errs, branches, check_branches = callbacks.get dim user_branches tyfam in
      (* Now we iterate through the remaining constructors, typechecking the corresponding branches and inserting them in the match tree. *)
      let branches, errs =
        List.fold_left
          (fun (branches, errs)
               ( constr,
                 (Checkable_branch { xs; body; env; argtys; index_terms } :
                   (dom, a, m, ij) checkable_branch) ) ->
            (* Create new De-Bruijn-level variables for the pattern variables to which the constructor is applied, and add corresponding De-Bruijn-index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
            let (Ext_tel
                   {
                     ctx = newctx;
                     env = newenv;
                     values = newvars;
                     normals = newnfs;
                     annotate;
                     comp;
                   }) =
              ext_tel ctx window env xs argtys in
            let perm = id_perm in
            let status =
              make_match_status status window plus_lock tm dim branches annotate comp None perm
                constr in
            (* Recurse into the "body" of the branch.  We catch errors and accumulate them so that later branches can continue to be checked and produce their own errors even if earlier ones fail, but we pass through the errors that are getting caught elsewhere. *)
            Reporter.try_with ~fatal:(fun e ->
                match e.message with
                | Missing_constructor_in_match _ -> fatal_diagnostic e
                | _ -> (branches, Snoc (errs, e)))
            @@ fun () ->
            match (body, motive) with
            (* In the synthesizing case, we might still have no motive, if all the synthesis failed.  In that case, the only reason we're going through this is to annotate the contexts of each branch. *)
            | Some body, None ->
                Annotate.ctx status newctx body;
                (branches, errs)
            | Some body, Some motive ->
                let cmotive = callbacks.use motive constr dim index_terms newenv newvars in
                let cbody = check status newctx body cmotive in
                ( branches
                  |> Constr.Map.add constr (Term.Branch { annotate; comp; perm; tm = cbody }),
                  errs )
            (* If there is no body, the user omitted this constructor, which is valid if and only if one of the pattern variables belongs to an empty type. *)
            | None, _ ->
                if any_empty newnfs then (branches |> Constr.Map.add constr Term.Refute, errs)
                else fatal (Missing_constructor_in_match constr))
          (branches, errs) check_branches in
      match errs with
      | Snoc _ -> fatal (Accumulated ("check_match_branches", errs))
      | Emp ->
          (* Finally, we check that all the abstractions used the correct symbol ↦ or ⤇ *)
          List.iter
            (fun b ->
              if not !(b.value) then fatal ?loc:b.loc (Zero_dimensional_cube_abstraction "match"))
            highers;
          ( Match { tm; window; plus_lock; dim; branches },
            Option.map (callbacks.return indices inst_args) motive ))
  | _ ->
      let (Locked (_, lctx)) = Ctx.lock ctx window in
      fatal ?loc (Matching_on_nondatatype (PVal (lctx, varty)))

(* Check a non-dependent match against a specified type. *)
and check_nondep_match : type dom window mode a b bm.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    (dom, bm, kinetic) term ->
    (dom, kinetic) value ->
    (dom, window, mode) Modality.t ->
    (b, mode, window, dom, bm) plus_lock ->
    (Constr.t, a branch) Abwd.t ->
    int located option ->
    bool ref located list ->
    (mode, kinetic) value ->
    Asai.Range.t option ->
    (mode, b, potential) term =
 fun status ctx tm varty window plus_lock brs i highers motive loc ->
  let result, _ =
    check_match_branches status ctx tm varty window plus_lock brs i highers loc
      (* Since the motive is already given, the callback can just return it. *)
      (Motive
         {
           get = (fun _ user_branches _ -> (Some motive, Emp, Constr.Map.empty, user_branches));
           use = (fun x _ _ _ _ _ -> x);
           return = (fun _ _ x -> x);
         }) in
  result

(* Try to synthesize a type from all the branches.  If any succeed, check the remaining branches against that synthesized type. *)
and synth_nondep_match : type mode a b.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    a synth located ->
    string located list located option ->
    (Constr.t, a branch) Abwd.t ->
    bool ref located list ->
    int located option ->
    (mode, b, potential) term * (mode, kinetic) value =
 fun status ctx tm window_name brs highers i ->
  (* First we synthesize the discriminee.  If that fails, we give up completely, as we don't even have a context in which to try synthesizing the branches. *)
  match get_window (Ctx.mode ctx) window_name with
  | Wrap (type dom window) (window : (dom, window, mode) Modality.t) -> (
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx window in
      let (tm, varty), loc = (synth (Kinetic `Nolet) lctx tm, tm.loc) in
      (* Now we define the callback that will try to synthesize a motive from one of the branches. *)
      let get : type m ij.
          m D.t ->
          (Constr.t * (dom, a, m, ij) checkable_branch) list ->
          dom normal Lazy.t option ref ->
          (mode, kinetic) value option
          * Code.t Asai.Diagnostic.t Bwd.t
          * (mode, b, m) Term.branch Constr.Map.t
          * (Constr.t * (dom, a, m, ij) checkable_branch) list =
       fun dim user_branches _ ->
        (* We split the branches into the synthesizing and non-synthesizing ones. *)
        let synth_branches, check_branches =
          List.partition_map
            (fun (c, (Checkable_branch { xs; body; env; argtys; index_terms } as cb)) ->
              match body with
              | Some { value = Synth sbody; loc } ->
                  let body = locate_opt loc sbody in
                  Left (c, Synthable_branch { xs; body; env; argtys; index_terms })
              | _ -> Right (c, cb))
            user_branches in
        (* We iterate through the synthesizing branches looking for the first one that succeeds at synthesizing, accumulating errors from the ones that fail. *)
        let rec find_synthing_branch errs = function
          | [] ->
              (* If they all fail, then we report the accumulated errors (we can't go on to the checking branches, since we don't have anything to even try to typecheck them against).  If there weren't any to begin with, we instead report their absence. *)
              let errs =
                if Bwd.is_empty errs then
                  Snoc (Emp, diagnostic (Nonsynthesizing "match without synthesizing branches"))
                else errs in
              (None, errs, Constr.Map.empty, [])
          | ( constr,
              (Synthable_branch { xs; body; env; argtys; index_terms = _ } :
                (dom, a, m, ij) synthable_branch) )
            :: brs ->
              (* This is the same preprocessing that's done for checking branches in check_match_branches. *)
              let (Ext_tel { ctx = newctx; annotate; comp; _ }) = ext_tel ctx window env xs argtys in
              let perm = id_perm in
              let status =
                make_match_status status window plus_lock tm dim Constr.Map.empty annotate comp None
                  perm constr in
              Annotate.ctx status newctx (locate_opt body.loc (Synth body.value));
              (* Trap errors and accumulate them, going on to look for other synthesizing branches. *)
              Reporter.try_with ~fatal:(fun e -> find_synthing_branch (Snoc (errs, e)) brs)
              @@ fun () ->
              let sbr, sty = synth status newctx body in
              (* The type synthesized is only valid for the whole match if it doesn't depend on the pattern variables.  We check that by reading it back into the original context. *)
              ( Reporter.try_with ~fatal:(fun d ->
                    match d.message with
                    | No_such_level _ ->
                        fatal ?loc:d.explanation.loc
                          (Invalid_synthesized_type
                             ("synthesizing branch of match", PVal (newctx, sty)))
                    | _ -> fatal_diagnostic d)
              @@ fun () -> ignore (readback_val ctx sty) );
              (* Finally, if we found a synthesizing branch that works, return the synthesized type, the accumulated errors, the successful typechecked branch, and the remaining synthesizing branches.  We don't need to deal again with any of the ones we've visited before the one that succeeded, as they all must have errored in order to get here, and we've accumulated their errors. *)
              ( Some sty,
                errs,
                Constr.Map.singleton constr (Term.Branch { annotate; comp; perm; tm = sbr }),
                brs ) in
        let motive, errs, branches, synth_branches = find_synthing_branch Emp synth_branches in
        (* We put the remaining synthesizing branches back on the front of the checking ones, and return them. *)
        let check_branches =
          List.fold_right
            (fun (c, Synthable_branch { xs; body; env; argtys; index_terms }) cbs ->
              let body = Some { value = Synth body.value; loc = body.loc } in
              (c, Checkable_branch { xs; body; env; argtys; index_terms }) :: cbs)
            synth_branches check_branches in
        (motive, errs, branches, check_branches) in
      (* Now using that callback, we pass off to the subroutine.  Since this match is non-dependent, the "use" and "return" callbacks can just return the type we have computed by synthesizing a branch. *)
      let result, motive =
        check_match_branches status ctx tm varty window plus_lock brs i highers loc
          (Motive { get; use = (fun x _ _ _ _ _ -> x); return = (fun _ _ x -> x) }) in
      match motive with
      | None -> fatal (Anomaly "synth_nondep_match: no synthesized type of match but no errors")
      | Some motive -> (result, motive))

(* Check a dependently typed match, with motive supplied by the user.  (Thus we have to typecheck the motive as well.)  *)
and synth_dep_match : type mode a b.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    a synth located ->
    string located list located option ->
    (Constr.t, a branch) Abwd.t ->
    bool ref located list ->
    a check located ->
    (mode, b, potential) term * (mode, kinetic) value =
 fun status ctx tm window_name brs highers motive ->
  (* We synthesize the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  match get_window (Ctx.mode ctx) window_name with
  | Wrap window -> (
      let (Locked (plus_lock, lctx)) = Ctx.lock ctx window in
      let (tm, varty), loc = (synth (Kinetic `Nolet) lctx tm, tm.loc) in
      let result, result_ty =
        check_match_branches status ctx tm varty window plus_lock brs None highers loc
          (* In this case when the motive is dependent, the definition of the motive callbacks is more involved. *)
          (Motive
             {
               get =
                 (fun _ user_branches tyfam ->
                   (* We typecheck the motive against the type of type families over the datatype and its indices.  Constructing this type of type families is what "motive_of_family" does. *)
                   let tyfam =
                     match !tyfam with
                     | Some tyfam -> Lazy.force tyfam
                     | None -> fatal (Anomaly "tyfam unset") in
                   let emotivety =
                     eval_term (Ctx.env ctx) (motive_of_family ctx window tyfam.tm tyfam.ty) in
                   let cmotive = check (Kinetic `Nolet) ctx motive emotivety in
                   let emotive = eval_term (Ctx.env ctx) cmotive in
                   (* Note that the motive object here is a *type family* value, not a single type.  Therefore, the "use" and "return" callbacks have to apply that function to appropriate arguments.  *)
                   (Some emotive, Emp, Constr.Map.empty, user_branches));
               use =
                 (fun emotive constr dim index_terms newenv newvars ->
                   (* To get the type at which to typecheck the body of a branch, we have to apply the general dependent motive to the indices of this constructor, its boundaries, and itself.  First we compute the indices. *)
                   let index_vals =
                     Vec.mmap (fun [ ixtm ] -> eval_with_boundary newenv ixtm) [ index_terms ] in
                   (* Now we compute the constructor and its boundaries.  TODO: Rather than building a cube and then immediately traversing it, it would be more efficient to call a function that just traverses all faces of some dimension. *)
                   let constr_vals =
                     CubeOf.build dim
                       {
                         build =
                           (fun fa ->
                             Value.Constr
                               ( constr,
                                 dom_sface fa,
                                 List.map
                                   (fun (Value.Modal (mu, s)) ->
                                     let (Filter_sface (fb, mu')) = Modality.filter_sface mu fa in
                                     Value.Modal (mu', CubeOf.subcube fb s))
                                   newvars ));
                       } in
                   (* Finally, we apply the motive to all of these arguments. *)
                   let result = Vec.fold_left (apply_singletons window) emotive index_vals in
                   apply_singletons window result constr_vals);
               return =
                 (fun indices inst_args emotive ->
                   (* We compute the output type of the match by applying the dependent motive to the discriminee's indices, boundary, and itself. *)
                   let result = Vec.fold_left (apply_singleton_nfs window) emotive indices in
                   let result = apply_singleton_tube_nfs window result inst_args in
                   apply_term result (Modality.filter_zero window)
                     (CubeOf.singleton (eval_term (Ctx.env lctx) tm)));
             }) in
      match result_ty with
      | None -> fatal (Anomaly "synth_dep_match: no type of match but no errors")
      | Some result_ty -> (result, result_ty))

(* Check a match against a well-behaved variable, which can only appear in a case tree and refines not only the goal but the context (possibly with permutation).  This duplicates some of the code from check_match_branches, but it is doing so many other things as well that I haven't tried to unify them. *)
and check_var_match : type dom modality mode a b bm.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    level ->
    (dom, bm) index ->
    (dom, kinetic) value ->
    (dom, modality, mode) Modality.t ->
    (b, mode, modality, dom, bm) plus_lock ->
    (Constr.t, a branch) Abwd.t ->
    a refutables option ->
    bool ref located list ->
    (mode, kinetic) value ->
    Asai.Range.t option ->
    (mode, b, potential) term =
 fun status ctx level index varty window plus brs refutables highers motive loc ->
  (* We look up the type of the discriminee, which must be a datatype, without any degeneracy applied outside, and at the same dimension as its instantiation. *)
  match view_type varty "check_var_match" with
  | Canonical
      (type hmode mn m n)
      (( name,
         Data
           (type j ij)
           ({
              dim;
              indices = Filled var_indices;
              constrs = data_constrs;
              discrete = _;
              recursive;
              tyfam;
              hints = _;
            } :
             (_, _, j, ij) data_args),
         ins,
         inst_args ) :
        hmode head * (dom, m, n) canonical * (mn, m, n) insertion * _) -> (
      let Eq = eq_of_ins_zero ins in
      check_window_transparency window data_constrs recursive;
      let tyfam =
        match !tyfam with
        | Some tyfam -> Lazy.force tyfam
        | None -> fatal (Anomaly "tyfam unset") in
      let tyfam_args : (D.zero, m, m, dom normal) TubeOf.t =
        match view_type tyfam.ty "check_var_match tyfam" with
        | Canonical (_, Pi _, _, tyfam_args) -> (
            match D.compare dim (TubeOf.inst tyfam_args) with
            | Neq -> fatal (Dimension_mismatch ("check_var_match", dim, TubeOf.inst tyfam_args))
            | Eq -> tyfam_args)
        | Canonical (_, UU (_mode, n), ins, tyfam_args) -> (
            let Eq = eq_of_ins_zero ins in
            match D.compare dim n with
            | Neq -> fatal (Dimension_mismatch ("check_var_match", dim, n))
            | Eq -> tyfam_args)
        | _ ->
            let (Locked (_, lctx)) = Ctx.lock ctx window in
            fatal (Show ("tyfam is not a type family", PVal (lctx, tyfam.ty))) in
      (* In our simple version of pattern-matching against a variable, the "indices" and all their boundaries must be distinct free variables with no degeneracies, so that in the branch for each constructor they can be set equal to the computed value of that index for that constructor (and in which they cannot occur).  This is a special case of the unification algorithm described in CDP "Pattern-matching without K" where the only allowed rule is "Solution".  Later we can try to enhance it with their full unification algorithm, at least for non-higher datatypes.  In addition, for a higher-dimensional match, the instantiation arguments must also all be distinct variables, distinct from the indices.  If any of these conditions fail, we raise an exception, catch it, emit a hint, and revert to doing a non-dependent match. *)
      let seen = Hashtbl.create 10 in
      let is_fresh (x : dom normal) =
        match x.tm with
        | Neu { head = Var { level; deg; key = _ }; args = Emp; value; ty = _ } -> (
            match force_eval value with
            | Unrealized ->
                (if Option.is_none (is_id_deg deg) then
                   let (Locked (_, lctx)) = Ctx.lock ctx window in
                   fatal
                     (Matching_wont_refine
                        ("index variable has degeneracy", Some (PNormal (lctx, x)))));
                (if Hashtbl.mem seen level then
                   let (Locked (_, lctx)) = Ctx.lock ctx window in
                   fatal
                     (Matching_wont_refine
                        ("duplicate variable in indices", Some (PNormal (lctx, x)))));
                Hashtbl.add seen level ();
                level
            | _ -> fatal (Anomaly "local variable bound to a potential term"))
        | _ ->
            let (Locked (_, lctx)) = Ctx.lock ctx window in
            fatal (Matching_wont_refine ("index is not a free variable", Some (PNormal (lctx, x))))
      in
      Reporter.try_with ~fatal:(fun d ->
          match d.message with
          | Matching_wont_refine (str, x) ->
              emit ?loc:d.explanation.loc (Matching_wont_refine (str, x));
              check_nondep_match status ctx (Term.Var index) varty window plus brs None highers
                motive loc
          | No_such_level x ->
              emit ?loc:d.explanation.loc
                (Matching_wont_refine ("index variable occurs in parameter", Some x));
              check_nondep_match status ctx (Term.Var index) varty window plus brs None highers
                motive loc
          | _ -> fatal_diagnostic d)
      @@ fun () ->
      let index_vars =
        Vec.mmap
          (fun [ tm ] -> CubeOf.mmap { map = (fun _ [ x ] -> is_fresh x) } [ tm ])
          [ var_indices ] in
      let inst_vars = TubeOf.mmap { map = (fun _ [ x ] -> is_fresh x) } [ inst_args ] in
      let constr_vars = TubeOf.plus_cube inst_vars (CubeOf.singleton level) in
      (* Now we also check that none of these free variables occur in the parameters.  We do this by altering the context to replace all these level variables with unknowns and doing a readback of the pre-indices type family into that context.  If the readback encounters one of the missing level variables, it fails with No_such_level; above we catch that, emit a hint, and fall back to matching against a term. *)
      (* TODO: This doesn't seem to be catching things it should, like attempted proofs of Axiom K; they go on and get caught by No_permutation instead. *)
      let ctx_noindices = Ctx.forget_levels ctx (Hashtbl.mem seen) in
      let (Locked (_, ctx_noindices)) = Ctx.lock ctx_noindices window in
      ignore (readback_nf ctx_noindices tyfam);
      (* If all of those checks succeed, we continue on the path of a variable match.  But note that this call is still inside the try_with, so it can still fail and revert back to a non-dependent term match. *)
      (* We start with a preprocesssing step that pairs each user-provided branch with the corresponding constructor information from the datatype. *)
      let user_branches = merge_branches name brs data_constrs in
      (* We now iterate through the constructors, typechecking the corresponding branches and inserting them in the match tree. *)
      let branches, errs =
        List.fold_left
          (fun (branches, errs)
               ( constr,
                 (Checkable_branch { xs; body; env; argtys; index_terms } :
                   (dom, a, m, ij) checkable_branch) ) ->
            (* Create new level variables for the pattern variables to which the constructor is applied, and add corresponding index variables to the context.  The types of those variables are specified in the telescope argtys, and have to be evaluated at the closure environment 'env' and the previous new variables (this is what ext_tel does).  For a higher-dimensional match, the new variables come with their boundaries in n-dimensional cubes. *)
            let (Ext_tel
                   {
                     ctx = newctx;
                     env = newenv;
                     values = newvars;
                     normals = newnfs;
                     annotate;
                     comp;
                   }) =
              ext_tel ctx window env xs argtys in
            (* Evaluate the "index_terms" at the new pattern variables, obtaining what the indices should be for the new term that replaces the match variable in the match body. *)
            let index_vals =
              Vec.mmap
                (fun [ ixtm ] ->
                  CubeOf.build dim
                    { build = (fun fa -> eval_term (act_env newenv (opt_op_of_sface fa)) ixtm) })
                [ index_terms ] in
            (* Assemble a term consisting of the constructor applied to the new variables, along with its boundary, and their types.  To compute their types, we have to extract the datatype applied to its parameters only, pass to boundaries if necessary, and then re-apply it to the new indices. *)
            let constr_tys = TubeOf.plus_cube tyfam_args (CubeOf.singleton tyfam) in
            let argtbl = Hashtbl.create 10 in
            let constr_nfs =
              CubeOf.mmap
                {
                  map =
                    (fun fa [ constrty ] ->
                      let k = dom_sface fa in
                      let tm =
                        Value.Constr
                          ( constr,
                            k,
                            List.map
                              (fun (Value.Modal (mu, s)) ->
                                let (Filter_sface (fb, mu')) = Modality.filter_sface mu fa in
                                Value.Modal (mu', CubeOf.subcube fb s))
                              newvars ) in
                      let ty =
                        inst
                          (Vec.fold_left
                             (fun f a ->
                               apply_term f
                                 (* Indices cannot have nontrivial modal dependence. *)
                                 (Modality.filter_id (Modality.src window) (dom_sface fa))
                                 (CubeOf.subcube fa a))
                             constrty.tm index_vals)
                          (TubeOf.build D.zero (D.zero_plus k)
                             {
                               build =
                                 (fun fb ->
                                   Hashtbl.find argtbl
                                     (SFace_of (comp_sface fa (sface_of_tface fb))));
                             }) in
                      let x = { tm; ty } in
                      Hashtbl.add argtbl (SFace_of fa) x;
                      x);
                }
                [ constr_tys ] in
            let constr_nf = CubeOf.find_top constr_nfs in
            (* Since "index_vals" is just a Bwv of Cubes of *values*, we extract the corresponding collection of *normals* from the type.  The main use of this will be to substitute for the index variables, so instead of assembling them into another Bwv of Cubes, we make a hashtable associating those index variables to the corresponding normals.  We also include in the same hashtable the lower-dimensional applications of the same constructor, to be substituted for the instantiation variables. *)
            match view_type constr_nf.ty "check_var_match (inner)" with
            | Canonical (_, Data { dim = constrdim; indices = Filled indices; _ }, ins, _) -> (
                let Eq = eq_of_ins_zero ins in
                match
                  ( D.compare constrdim dim,
                    Fwn.compare (Vec.length index_terms) (Vec.length indices) )
                with
                | Neq, _ -> fatal (Anomaly "created datatype has wrong dimension")
                | _, Neq -> fatal (Anomaly "created datatype has wrong number of indices")
                | Eq, Eq -> (
                    (* The values being bound live at the domain mode of the window modality. *)
                    let ctxmode = Modality.src window in
                    let new_vals = Hashtbl.create 10 in
                    CubeOf.miter
                      { it = (fun _ [ v; c ] -> Hashtbl.add new_vals v c) }
                      [ constr_vars; constr_nfs ];
                    Vec.miter
                      (fun [ vs; cs ] ->
                        CubeOf.miter
                          { it = (fun _ [ v; c ] -> Hashtbl.add new_vals v c) }
                          [ vs; cs ])
                      [ index_vars; indices ];
                    (* Now we let-bind the match variable to the constructor applied to these new variables, the "index_vars" to the index values, and the inst_vars to the boundary constructor values.  The operation bind_some automatically substitutes these new values into the types and values of other variables in the context, and reorders it if necessary so that each variable only depends on previous ones. *)
                    match Bindsome.bind_some (ctxmode, new_vals) newctx with
                    | None ->
                        fatal (Matching_wont_refine ("no consistent permutation of context", None))
                    | Bind_some { checked_perm; oldctx; newctx } -> (
                        (* We readback the index and instantiation values into this new context and discard the result, catching No_such_level to turn it into a user Error.  This has the effect of doing an occurs-check that none of the index variables occur in any of the index values.  This is a bit less general than the CDP Solution rule, which (when applied one variable at a time) prohibits only cycles of occurrence.  Note that this exception is still caught by check_var_match, above, causing a fallback to term matching. *)
                        ( Reporter.try_with ~fatal:(fun d ->
                              match d.message with
                              | No_such_level x ->
                                  fatal ?loc:d.explanation.loc
                                    (Matching_wont_refine
                                       ("free index variable occurs in inferred index value", Some x))
                              | _ -> fatal_diagnostic d)
                        @@ fun () ->
                          let (Locked (_, oldlctx)) = Ctx.lock oldctx window in
                          Hashtbl.iter (fun _ v -> ignore (readback_nf oldlctx v)) new_vals );
                        (* The type of the match must be specialized in the branches by substituting different constructors for the match variable, as well as the index values for the index variables, and lower-dimensional versions of each constructor for the instantiation variables.  Thus, we readback-eval this type into the new context, to obtain the type at which the branch body will be checked. *)
                        let newty = eval_term (Ctx.env newctx) (readback_val oldctx motive) in
                        (* Now we have to modify the "status" data by readback-eval on the arguments and adding a hypothesized current branch to the match.  *)
                        let status =
                          make_match_status status window plus (Term.Var index) dim branches
                            annotate comp
                            (Some (oldctx, newctx))
                            checked_perm constr in
                        (* Finally, we typecheck the "body" of the branch, if the user supplied one. *)
                        match body with
                        | Some body ->
                            (* We catch and accumulate errors so that later branches can continue to be checked and produce their own errors even if earlier ones fail, but we pass through the errors that are getting caught elsewhere. *)
                            Reporter.try_with ~fatal:(fun e ->
                                match e.message with
                                | Missing_constructor_in_match _ -> fatal_diagnostic e
                                | _ -> (branches, Snoc (errs, e)))
                            @@ fun () ->
                            let branch = check status newctx body newty in
                            ( branches
                              |> Constr.Map.add constr
                                   (Term.Branch { annotate; comp; perm = checked_perm; tm = branch }),
                              errs )
                        (* If not, then we look for something to refute. *)
                        | None ->
                            (* First we check whether any of the new pattern variables created by this match belong to an empty datatype. *)
                            if
                              any_empty newnfs
                              ||
                              (* Otherwise, we check the stored "refutables", which include all the previous and succeeding pattern variables. *)
                              List.fold_left
                                (fun s x ->
                                  if s then true
                                  else
                                    let _, sty = synth (Kinetic `Nolet) newctx x in
                                    is_empty sty)
                                false
                                (Option.fold
                                   ~some:(fun r -> r.refutables (Namevec.bplus xs))
                                   ~none:[] refutables)
                              (* If we found something to refute, we mark this branch as refuted in the compiled match. *)
                            then (branches |> Constr.Map.add constr Term.Refute, errs)
                            else fatal (Missing_constructor_in_match constr))))
            | _ -> fatal (Anomaly "created datatype is not a datatype with all its indices"))
          (Constr.Map.empty, Emp) user_branches in
      match errs with
      | Snoc _ -> fatal (Accumulated ("check_var_match", errs))
      | Emp ->
          List.iter
            (fun b ->
              if not !(b.value) then fatal ?loc:b.loc (Zero_dimensional_cube_abstraction "match"))
            highers;
          Match { window; plus_lock = plus; tm = Term.Var index; dim; branches })
  | _ ->
      let (Locked (_, lctx)) = Ctx.lock ctx window in
      fatal ?loc (Matching_on_nondatatype (PVal (lctx, varty)))

and make_match_status : type dom window mode annotations a am b ab c n x y z.
    (mode, a, potential) status ->
    (dom, window, mode) Modality.t ->
    (a, mode, window, dom, am) plus_lock ->
    (dom, am, kinetic) term ->
    n D.t ->
    (mode, a, n) Term.branch Constr.Map.t ->
    (n, mode, annotations, mode, mode, b, mode) VarAnnotate.fwd_t ->
    (mode, b, mode, a, unit, ab) Tctx.bcomp ->
    ((mode, x, z) Ctx.t * (mode, y, z) Ctx.t) option ->
    (c, ab) permute ->
    Constr.t ->
    (mode, c, potential) status =
 fun status window plus_lock newtm dim branches annotate comp eval_readback perm constr ->
  let (Potential
         (type hm d any)
         ((head, args, hyp) :
           (hm, d) potential_head
           * (hm, mode, any) apps
           * ((mode, a, potential) term -> (hm, d, potential) term))) =
    status in
  let head, apps =
    match eval_readback with
    | Some (oldctx, newctx) ->
        (* The head is transformed at the bottom of the spine recursion, where the accumulated locks put the contexts at its mode. *)
        let rec erapps : type m2 any2 x1 z1 k.
            (m2, x1, z1) Ctx.t ->
            (m2, k, z1) env ->
            (hm, m2, any2) apps ->
            (hm, d) potential_head * (hm, m2, any2) apps =
         fun oldctx newenv -> function
           | Emp ->
               let (erhead : (hm, d) potential_head) =
                 match head with
                 | Meta (meta, metaenv) ->
                     let (Plus qn) = D.plus (dim_env metaenv) in
                     Meta
                       ( meta,
                         eval_env newenv qn
                           (readback_env oldctx metaenv (Global.find_meta meta).termctx) )
                 | Constant (c, cmode, dim) -> Constant (c, cmode, dim) in
               (erhead, Emp)
           | Arg (rest, filter, xs, ins) ->
               let modality = Modality.filter_modality filter in
               let (Locked (plus, loldctx)) = Ctx.lock oldctx modality in
               let lnewenv = key_env newenv (Modalcell.id modality) plus in
               let erhead, errest = erapps oldctx newenv rest in
               ( erhead,
                 Arg
                   ( errest,
                     filter,
                     CubeOf.mmap
                       {
                         map =
                           (fun _ [ x ] ->
                             let tm = eval_term lnewenv (readback_nf loldctx x) in
                             let ty = eval_term lnewenv (readback_val loldctx x.ty) in
                             { tm; ty });
                       }
                       [ xs ],
                     ins ) )
           | Field (rest, filter, x, y, z) ->
               (* The spine inside a modal field projection lives behind a lock by the left adjoint. *)
               let fm = Modality.filter_modality filter in
               let (Locked (plus, loldctx)) = Ctx.lock oldctx fm in
               let lnewenv = key_env newenv (Modalcell.id fm) plus in
               let erhead, errest = erapps loldctx lnewenv rest in
               (erhead, Field (errest, filter, x, y, z))
           | Inst _ -> fatal (Anomaly "inst in make_match_status") in
        erapps oldctx (Ctx.env newctx) args
    | None -> (head, args) in
  let hyp tm =
    let branches = branches |> Constr.Map.add constr (Term.Branch { annotate; comp; perm; tm }) in
    hyp (Term.Match { window; plus_lock; tm = newtm; dim; branches }) in
  Potential (head, apps, hyp)

(* Try matching against all the supplied terms with zero branches, producing an empty match if any succeeds and raising an error if none succeed.  Each term carries its own optional window modality. *)
and check_refute : type mode a b.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    (a synth located * string located list located option) list ->
    (mode, kinetic) value ->
    [ `Explicit | `Implicit ] ->
    Constr.t option ->
    (mode, b, potential) term =
 fun status ctx tms ty i missing ->
  match tms with
  | [] -> (
      match i with
      | `Implicit -> fatal (Anomaly "no discriminees to refute")
      | `Explicit -> fatal Invalid_refutation)
  (* If all the possibilities fail, we want to report a "missing constructor" error for the particular constructor supplied as an argument, if any, which comes from the first place where the refutation began. *)
  | [ (tm, window_name) ] ->
      let (Wrap window) = get_window (Ctx.mode ctx) window_name in
      let (Locked (plus, wctx)) = Ctx.lock ctx window in
      let stm, sty = synth (Kinetic `Nolet) wctx tm in
      Reporter.try_with
        (fun () -> check_nondep_match status ctx stm sty window plus Emp None [] ty tm.loc)
        ~fatal:(fun d ->
          match d.message with
          | Missing_constructor_in_match c -> (
              match (i, missing) with
              | `Explicit, _ -> fatal Invalid_refutation
              | `Implicit, Some missing -> fatal (Missing_constructor_in_match missing)
              | `Implicit, None -> fatal (Missing_constructor_in_match c))
          | _ -> fatal_diagnostic d)
  | (tm, window_name) :: (_ :: _ as tms) ->
      let (Wrap window) = get_window (Ctx.mode ctx) window_name in
      let (Locked (plus, wctx)) = Ctx.lock ctx window in
      let stm, sty = synth (Kinetic `Nolet) wctx tm in
      Reporter.try_with
        (fun () -> check_nondep_match status ctx stm sty window plus Emp None [] ty tm.loc)
        ~fatal:(fun d ->
          match d.message with
          | Missing_constructor_in_match c ->
              check_refute status ctx tms ty i (Some (Option.value missing ~default:c))
          | _ -> fatal_diagnostic d)

(* Try empty-matching against each successive domain in an iterated pi-type.  For higher-dimensional pi-types, try empty-matching against each variable in the abstraction cube. *)
and check_empty_match_lam : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    [ `First | `Notfirst ] ->
    (mode, b, potential) term =
 fun ctx ty first ->
  match view_type ty "check_empty_match_lam" with
  | Canonical
      (type hmode kn k n)
      ((_, Pi { x = _; filter; doms; cods }, ins, tyargs) :
        hmode head
        * (mode, k, n) canonical
        * (kn, k, n) insertion
        * (D.zero, kn, kn, mode normal) TubeOf.t) -> (
      let modality = Modality.filter_modality filter in
      (* MODALTODO: If the modality is nonidentity, it would be a window modality. *)
      match Modality.compare_id modality with
      | Neq -> fatal (Unimplemented "nontrivial window modality in empty match")
      | Eq -> (
          let Eq = eq_of_ins_zero ins in
          (* Since the modality is the identity, the filtered dimension equals the outer dimension. *)
          let Eq = Modality.eq_of_filter_id filter in
          let dim = CubeOf.dim doms in
          let newargs, newnfs = dom_vars ctx modality doms in
          let output = tyof_app cods tyargs filter newargs in
          let module S = struct
            type 'c t =
              | Ok : (mode, kinetic) value option * (a, 'c, 'ac) N.plus * k sface_of option -> 'c t
          end in
          let module Build = NICubeOf.Traverse (S) in
          match
            Build.build_left dim
              {
                build =
                  (fun fb -> function
                    | Ok (firstty, ab, fa) ->
                        let ty = (Binding.value (CubeOf.find newnfs fb)).ty in
                        let firstty = Option.value firstty ~default:ty in
                        if is_empty ty then
                          Fwrap
                            ( NFamOf (`Anon (View.hints_of_ty ty)),
                              Ok (Some firstty, Suc ab, Some (SFace_of fb)) )
                        else
                          Fwrap (NFamOf (`Anon (View.hints_of_ty ty)), Ok (Some firstty, Suc ab, fa)));
              }
              (Ok (None, Zero, None))
          with
          | Wrap (names, Ok (firstty, af, fa)) -> (
              let xs = Variables (D.zero, D.zero_plus dim, names) in
              let ctx = Ctx.vis ctx filter D.zero (D.zero_plus dim) names newnfs af in
              match (fa, first) with
              | Some (SFace_of fa), _ ->
                  Lam
                    ( xs,
                      dim,
                      filter,
                      Match
                        {
                          window = Modality.id (Modality.tgt modality);
                          plus_lock = plus_no_lock (Modality.tgt modality);
                          tm =
                            Var
                              (Index (Now, fa, filter, plus_with_no_locks (Modality.tgt modality)));
                          dim;
                          branches = Constr.Map.empty;
                        } )
              | None, `Notfirst ->
                  Term.Lam (xs, dim, filter, check_empty_match_lam ctx output `Notfirst)
              | None, `First ->
                  Reporter.try_with
                    (fun () ->
                      Term.Lam (xs, dim, filter, check_empty_match_lam ctx output `Notfirst))
                    ~fatal:(fun d ->
                      match d.message with
                      | Invalid_refutation -> (
                          let firstty = firstty <|> Anomaly "missing firstty in checking []" in
                          match view_type firstty "is_empty" with
                          | Canonical (_, Data { constrs; _ }, _, _) ->
                              fatal (Missing_constructor_in_match (fst (Bwd_extra.head constrs)))
                          | _ -> fatal (Matching_on_nondatatype (PVal (ctx, firstty))))
                      | _ -> fatal_diagnostic d))))
  | _ -> fatal Invalid_refutation

and is_empty : type mode. (mode, kinetic) value -> bool =
 fun varty ->
  match view_type varty "is_empty" with
  | Canonical (_, Data { constrs = Emp; _ }, _, _) -> true
  | _ -> false

and any_empty : type mode n. (n, mode) modal_binding_cube list -> bool =
 fun nfss ->
  let module CM = CubeOf.Monadic (Monad.State (Bool)) in
  List.fold_left
    (fun s (Modal (_modality, nfs)) ->
      snd (CM.miterM { it = (fun _ [ x ] s -> ((), s || is_empty (Binding.value x).ty)) } [ nfs ] s))
    false nfss

and check_data : type mode a b i.
    discrete:unit Constant.Map.t option ->
    recursive:Positivity.recursion ->
    hints:hints ->
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    (mode, kinetic) value ->
    i Fwn.t ->
    (Constr.t, (mode, b, i) Term.dataconstr) Abwd.t ->
    (Constr.t * a Raw.dataconstr located) list ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    (mode, b, potential) term =
 fun ~discrete ~recursive ~hints status ctx ty num_indices checked_constrs raw_constrs errs ->
  match (raw_constrs, status) with
  | [], Potential _ -> (
      match errs with
      | Snoc _ -> fatal (Accumulated ("check_data", errs))
      | Emp ->
          (* If we get to this point and discreteness is still a possibility, we mark it as "Maybe" discrete.  Later, after all the types in a mutual block are checked, if they're all discrete we go through and change the "Maybe"s to "Yes"es.  *)
          let discrete = Option.fold ~none:`No ~some:(fun _ -> `Maybe) discrete in
          Canonical
            (Data { indices = num_indices; constrs = checked_constrs; discrete; recursive; hints }))
  | ( (c, { value = Dataconstr (args, output); loc }) :: raw_constrs,
      Potential (head, current_apps, hyp) ) -> (
      with_loc loc @@ fun () ->
      (* Temporarily bind the current constant to the up-until-now value, for recursive purposes, and also for specifying the output types for indexed inductive families (and presumably, one day, for higher inductive types). *)
      run_with_definition head
        (hyp
           (Term.Canonical
              (Data
                 {
                   indices = num_indices;
                   constrs = checked_constrs;
                   discrete = `No;
                   recursive = `Recursive;
                   hints;
                 })))
        Emp
      @@ fun () ->
      match (Abwd.find_opt c checked_constrs, output) with
      | Some _, _ -> fatal (Duplicate_constructor_in_data c)
      | None, Some output ->
          let disc, crec, (checked_constrs : (Constr.t, (mode, b, i) Term.dataconstr) Abwd.t), errs
              =
            Reporter.try_with ~fatal:(fun e -> (true, `Recursive, checked_constrs, Snoc (errs, e)))
            @@ fun () ->
            (* The argument telescope is checked in an occurrence-analysis scope, to detect whether this constructor is recursive.  The output type is NOT included in the scope: its head is by definition the current datatype, and occurrences there are not recursion. *)
            let (Checked_tel (args, newctx), disc), crec =
              Positivity.scope @@ fun () -> check_tel ?discrete ctx args in
            (* Note the type of each field is checked *kinetically*: it's not part of the case tree. *)
            let coutput = check (Kinetic `Nolet) newctx output (universe (Ctx.mode ctx) D.zero) in
            let err = Code.Invalid_constructor_type (c, Left "head must be current datatype") in
            match eval_term (Ctx.env newctx) coutput with
            | Neu { head = Const { name = out_head; ins }; args = out_apps; value = _; ty = _ } -> (
                match head with
                | Constant (cc, _, n) when cc = out_head && Option.is_some (is_id_ins ins) -> (
                    match D.compare_zero n with
                    | Pos _ ->
                        fatal ?loc:output.loc
                          (Unimplemented "indexed inductive types nested inside higher comatches")
                    | Zero -> (
                        let (Wrap indices) = get_indices newctx c current_apps out_apps output.loc in
                        match Fwn.compare (Vec.length indices) num_indices with
                        | Eq ->
                            ( disc,
                              crec,
                              checked_constrs |> Abwd.add c (Term.Dataconstr { args; indices }),
                              errs )
                        | _ ->
                            (* I think this shouldn't ever happen, no matter what the user writes, since we know at this point that the output is a full application of the correct constant, so it must have the right number of arguments. *)
                            fatal (Anomaly "length of indices mismatch")))
                | _ -> fatal ?loc:output.loc err)
            | _ -> fatal ?loc:output.loc err in
          check_data
            ~discrete:(if disc then discrete else None)
            ~recursive:(Positivity.merge recursive crec) ~hints status ctx ty num_indices
            checked_constrs raw_constrs errs
      | None, None -> (
          match num_indices with
          | Zero ->
              let ( disc,
                    crec,
                    (checked_constrs : (Constr.t, (mode, b, i) Term.dataconstr) Abwd.t),
                    errs ) =
                Reporter.try_with ~fatal:(fun e ->
                    (true, `Recursive, checked_constrs, Snoc (errs, e)))
                @@ fun () ->
                let (Checked_tel (args, _), disc), crec =
                  Positivity.scope @@ fun () -> check_tel ?discrete ctx args in
                ( disc,
                  crec,
                  checked_constrs |> Abwd.add c (Term.Dataconstr { args; indices = [] }),
                  errs ) in
              check_data
                ~discrete:(if disc then discrete else None)
                ~recursive:(Positivity.merge recursive crec) ~hints status ctx ty Fwn.zero
                checked_constrs raw_constrs errs
          | Suc _ -> fatal (Missing_constructor_type c)))

(* Get the indices from the codomain of a constructor's type. *)
and get_indices : type mode hmode1 hmode2 a b any1 any2.
    (mode, a, b) Ctx.t ->
    Constr.t ->
    (hmode1, mode, any1) apps ->
    (hmode2, mode, any2) apps ->
    Asai.Range.t option ->
    (mode, b, kinetic) term Vec.wrapped =
 fun ctx c current output loc ->
  with_loc loc @@ fun () ->
  let (Split_apps (output_params, output_indices)) =
    split_apps_at_length current output
    <|> Invalid_constructor_type (c, Left "wrong number of index arguments") in
  (* We walk the remaining forward sequence of applications, which must consist of ordinary Args at the ambient mode: Fields (in particular modal ones) cannot be indices.  The mode equation between the start of the remainder and the ambient mode only becomes available once we reach the end of the sequence, so we return it from the recursion. *)
  let rec go : type m1. (m1, mode) Fwd_app.fwd -> (m1, mode) Eq.t * (mode, b, kinetic) term list =
    function
    | Nil -> (Eq, [])
    | Cons
        ( Fwd_app.Arg
            (type dom modality n k m mk)
            ((filter, arg, ins) :
              (dom, modality, m1, n, m) Modality.filter_dim
              * (n, dom normal) CubeOf.t
              * (mk, m, k) insertion),
          rest ) -> (
        let Eq, tms = go rest in
        let modality = Modality.filter_modality filter in
        match (is_id_ins ins, Modality.compare_id modality, D.compare (CubeOf.dim arg) D.zero) with
        | Some _, Eq, Eq ->
            (Eq, (readback_nf ctx (CubeOf.find_top arg) : (mode, b, kinetic) term) :: tms)
        | None, _, _ -> fatal (Invalid_constructor_type (c, Left "no degeneracies are allowed"))
        | _, Neq, _ ->
            fatal (Invalid_constructor_type (c, Left "no modal applications are allowed"))
        | _, _, Neq ->
            fatal (Invalid_constructor_type (c, Left "applications must be zero-dimensional")))
    | Cons (Field _, _) -> fatal (Anomaly "field is not an index") in
  let Eq, tms = go output_indices in
  match equal_apps ctx current output_params with
  | None -> fatal (Invalid_constructor_type (c, Left "unequal parameters"))
  | Some (Error why) -> fatal (Invalid_constructor_type (c, Right why))
  | Some (Ok ()) -> Vec.of_list tms

(* The common prefix of checking a codatatype or record type, which returns a (cube of) variables belonging to the up-until-now type so that later fields can refer to earlier ones.  It also dynamically binds the current constant or metavariable, if possible, to that value for recursive purposes.  Since this binding has to scope over the rest of the functions that are specific to codata or records, it uses CPS. *)
and with_codata_so_far : type mode a b n c et.
    (mode, b, potential) status ->
    (potential, et) eta ->
    (mode, a, b) Ctx.t ->
    opacity ->
    hints ->
    n D.t ->
    (D.zero, n, n, mode normal) TubeOf.t ->
    (mode * b * n * et) Term.CodatafieldAbwd.t ->
    (mode, n, n, b, et) Fibrancy.Codata.t ->
    has_higher_fields:unit option ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    ((n, mode Ctx.Binding.t) CubeOf.t -> (mode, b, potential) term -> c) ->
    c =
 fun (Potential (h, args, hyp)) eta ctx opacity hints dim tyargs checked_fields (Fibrancy fibrancy)
     ~has_higher_fields errs cont ->
  let mode = Ctx.mode ctx in
  let domvars, termctx =
    match errs with
    | Emp ->
        (* We can always create a constant with the (0,0,0) insertion, even if its dimension is actually higher. *)
        let head = head_of_potential h in
        let fibrancy_fields = Fibrancy.Codata.finish mode checked_fields fibrancy in
        let idm = Modality.id (Ctx.mode ctx) in
        let rec domvars () =
          let value =
            eval_codata (Ctx.env ctx) eta opacity hints dim
              (lazy (termctx ()))
              checked_fields fibrancy_fields in
          let prev_ety =
            Neu { head; args; value = ready value; ty = lazy (inst (universe mode dim) tyargs) }
          in
          snd
            (dom_vars ctx idm
               (TubeOf.plus_cube
                  (TubeOf.mmap { map = (fun _ [ nf ] -> nf.tm) } [ tyargs ])
                  (CubeOf.singleton prev_ety)))
        and termctx () =
          let newctx = Ctx.cube_vis ctx (Modality.filter_id mode dim) None (domvars ()) in
          (* We don't spend the effort to readback the termctx unless the codatatype has higher fields, since it's only needed in that case (to read back the environment). *)
          Option.map (fun () -> readback_ctx newctx) has_higher_fields in
        (domvars (), termctx ())
    | Snoc _ ->
        let msg =
          match eta with
          | Eta -> "record dependent"
          | Noeta -> "codata dependent" in
        (CubeOf.build dim { build = (fun _ -> Ctx.Binding.error (Accumulated (msg, Emp))) }, None)
  in
  let codataterm =
    Term.Canonical
      (Codata
         { eta; opacity; hints; dim; fields = checked_fields; termctx; fibrancy; is_glue = None })
  in
  run_with_definition h (hyp codataterm) errs @@ fun () -> cont domvars codataterm

and check_codata : type mode a b n et.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    opacity ->
    (potential, et) eta ->
    hints ->
    (D.zero, n, n, mode normal) TubeOf.t ->
    (mode * b * n * et) Term.CodatafieldAbwd.t ->
    (mode, n, n, b, et) Fibrancy.Codata.t ->
    (Field.wrapped * a Raw.codatafield) list ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    has_higher_fields:unit option ->
    (mode, b, potential) term =
 fun status ctx opacity eta hints tyargs checked_fields fibrancy raw_fields errs
     ~has_higher_fields ->
  let dim = TubeOf.inst tyargs in
  match raw_fields with
  | [] -> (
      match errs with
      | Emp ->
          with_codata_so_far status eta ctx opacity hints dim tyargs checked_fields fibrancy
            ~has_higher_fields errs
          @@ fun _ codataterm -> codataterm
      | Snoc _ -> fatal (Accumulated ("check_codata", errs)))
  | (Wrap fld, Codatafield (x, lock, self_ty, rty)) :: raw_fields -> (
      with_codata_so_far status eta ctx opacity hints dim tyargs checked_fields fibrancy
        ~has_higher_fields errs
      @@ fun domvars _ ->
      (* If a type was given for the self variable, it must be equal to the current codatatype with its parameters. *)
      (match self_ty with
      | Some self_ty -> (
          let cself_ty = check (Kinetic `Nolet) ctx self_ty (universe (Ctx.mode ctx) D.zero) in
          let eself_ty = eval_term (Ctx.env ctx) cself_ty in
          let err : Code.t =
            Invalid_self_variable_type (fld, Left ("head must be current " ^ record_or_codata eta))
          in
          with_loc self_ty.loc @@ fun () ->
          match (eself_ty, status) with
          | ( Neu { head = Const { name; ins = _ }; args; value = _; ty = _ },
              Potential (Constant (pname, _, _), pargs, _) ) ->
              if name = pname then
                match equal_apps ctx args pargs with
                | None -> fatal (Invalid_self_variable_type (fld, Left "unequal parameters"))
                | Some (Error why) -> fatal (Invalid_self_variable_type (fld, Right why))
                | Some (Ok ()) -> ()
              else fatal err
          | _ -> fatal err)
      | None -> ());
      let newctx = Ctx.cube_vis ctx (Modality.filter_id (Ctx.mode ctx) dim) x domvars in
      (* A lower field and a higher field can't share a name, since projections at that name would be ambiguous. *)
      let check_name_clash () =
        match CodatafieldAbwd.find_string_opt checked_fields (Field.to_string fld) with
        | Some (CodatafieldAbwd.Entry (fld', _)) -> (
            match (D.compare_zero (Field.dim fld), D.compare_zero (Field.dim fld')) with
            | Zero, Pos _ | Pos _, Zero ->
                fatal (Lower_and_higher_methods_in_codata (Field.to_string fld))
            | _ -> ())
        | None -> () in
      (* A modal field is specified by giving the left adjoint of its adjunction as a locking annotation on the self variable; we ask the mode theory whether that modality is sinister to obtain the adjunction data.  An unannotated field is modal over the identity adjunction. *)
      let get_adjunction () : mode Modalcell.any_adjunction =
        match lock with
        | None -> Any_adjunction (Modalcell.id_adjunction (Ctx.mode ctx))
        | Some lockname -> (
            match Modality.of_name_src lockname.value (Ctx.mode ctx) with
            | Error e -> modality_fatal "field locking annotation" (e :> modality_error)
            | Ok (Wrap f) -> (
                match Modalcell.sinister f with
                | Some (Sinister adj) -> Any_adjunction adj
                | None -> fatal (Modality_not_sinister f))) in
      match (D.compare_zero (Field.dim fld), D.compare_zero (TubeOf.inst tyargs), eta) with
      | Zero, _, _ ->
          (* Zero-dimensional field *)
          let checked_fields, fibrancy, errs =
            Reporter.try_with ~fatal:(fun e -> (checked_fields, fibrancy, Snoc (errs, e)))
            @@ fun () ->
            check_name_clash ();
            let (Any_adjunction adj) = get_adjunction () in
            let (Adjunction { right; _ }) = adj in
            (* The type of a modal field is checked in a context locked by the right adjoint. *)
            let (Locked (plus_lock, lctx)) = Ctx.lock newctx right in
            (* Note the type of each field is checked *kinetically*: it's not part of the case tree. *)
            let cty = check (Kinetic `Nolet) lctx rty (universe (Modality.src right) D.zero) in
            let entry = CodatafieldAbwd.Entry (fld, Codatafield.Lower (adj, plus_lock, cty)) in
            ( Snoc (checked_fields, entry),
              Fibrancy.Codata.add_field (Ctx.mode ctx) fibrancy entry,
              errs ) in
          check_codata status ctx opacity eta hints tyargs checked_fields fibrancy raw_fields errs
            ~has_higher_fields
      | Pos _, Zero, Noeta -> (
          match lock with
          | Some _ -> fatal (Unimplemented "modal higher fields")
          | None ->
              (* Higher-dimensional field, currently requires a zero-dimensional codatatype (non-Gel). *)
              let checked_fields, errs =
                Reporter.try_with ~fatal:(fun e -> (checked_fields, Snoc (errs, e))) @@ fun () ->
                check_name_clash ();
                let (Degctx (plusmap, degctx, _)) = degctx newctx (Field.dim fld) in
                let cty = check (Kinetic `Nolet) degctx rty (universe (Ctx.mode ctx) D.zero) in
                (Snoc (checked_fields, Entry (fld, Codatafield.Higher (plusmap, cty))), errs) in
              check_codata status ctx opacity eta hints tyargs checked_fields fibrancy raw_fields
                errs ~has_higher_fields)
      | Pos _, Zero, Eta -> fatal (Unimplemented "higher fields in record types")
      | Pos _, Pos _, _ -> fatal (Unimplemented "higher fields in higher-dimensional codatatypes"))

and check_record : type mode a f1 f2 f af d acd b n.
    (mode, b, potential) status ->
    n D.t ->
    (mode, a, b) Ctx.t ->
    opacity ->
    hints ->
    (D.zero, n, n, mode normal) TubeOf.t ->
    (N.zero, n, binder_name, f1) NICubeOf.t ->
    (D.zero Field.t * string, f2) Bwv.t ->
    (f1, f2, f) N.plus ->
    (a, f, af) N.plus ->
    (mode * b * n * has_eta) Term.CodatafieldAbwd.t ->
    (mode, n, n, b, has_eta) Fibrancy.Codata.t ->
    (af, d, acd) Raw.tel ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    (mode, b, potential) term =
 fun status dim ctx opacity hints tyargs vars ctx_fields fplus af checked_fields fibrancy raw_fields
     errs ->
  match raw_fields with
  | Emp -> (
      match errs with
      | Snoc _ -> fatal (Accumulated ("check_record", errs))
      | Emp ->
          let fields, Fibrancy fibrancy = (checked_fields, fibrancy) in
          Term.Canonical
            (Codata
               { eta = Eta; opacity; hints; dim; fields; termctx = None; fibrancy; is_glue = None })
      )
  | Ext (None, _, _, _) -> fatal (Anomaly "unnamed field in check_record")
  | Ext (Some name, modality, rty, raw_fields) ->
      with_codata_so_far status Eta ctx opacity hints dim tyargs checked_fields fibrancy
        ~has_higher_fields:None errs
      @@ fun domvars _ ->
      let fld = Field.intern name D.zero in
      let checked_fields, fibrancy, ctx_fields, errs =
        Reporter.try_with ~fatal:(fun e ->
            (checked_fields, fibrancy, Bwv.Snoc (ctx_fields, (fld, name)), Snoc (errs, e)))
        @@ fun () ->
        match Modality.of_name_tgt (Ctx.mode ctx) modality.value with
        | Error e -> modality_fatal "field annotation" (e :> modality_error)
        | Ok (Wrap modality) -> (
            match Modality.compare_id modality with
            (* MODALTODO: Records with modal fields must currently be defined using self-variable syntax (which goes through check_codata).  An alternative would be to allow annotating a telescope-style record field with the *right* adjoint, testing that it is a declared right adjoint ("dextrous"); this is how we would get negative modalities. *)
            | Neq -> fatal (Unimplemented "modal record fields in telescope syntax")
            | Eq ->
                let newctx = Ctx.vis_fields ctx vars domvars ctx_fields fplus af in
                let cty = check (Kinetic `Nolet) newctx rty (universe (Ctx.mode ctx) D.zero) in
                let entry =
                  CodatafieldAbwd.Entry
                    ( fld,
                      Codatafield.Lower
                        (Modalcell.id_adjunction (Ctx.mode ctx), plus_no_lock (Ctx.mode ctx), cty)
                    ) in
                ( Snoc (checked_fields, entry),
                  Fibrancy.Codata.add_field (Ctx.mode ctx) fibrancy entry,
                  Bwv.Snoc (ctx_fields, (fld, name)),
                  errs )) in
      check_record status dim ctx opacity hints tyargs vars ctx_fields (Suc fplus) (Suc af)
        checked_fields fibrancy raw_fields errs

and check_struct : type mode a b c d s m n mn et.
    (mode, b, s) status ->
    (s, et) eta ->
    (mode, a, b) Ctx.t ->
    (* The type we are checking against *)
    (mode, kinetic) value ->
    (* m is the dimension to which that type has been substituted, and n is the Gel dimension of that type. *)
    m D.t ->
    (m, n, mn) D.plus ->
    (mode, m, n, d, c, et) codata_args ->
    (D.zero, mn, mn, mode normal) TubeOf.t ->
    (* The fields supplied by the user *)
    ((string * string list) option, [ `Normal | `Cube ] located * a check located) Abwd.t ->
    (mode, b, s) term =
 fun status eta ctx ty m mn ({ fields; _ } as codata_args) tyargs tms ->
  (* The type of each record field, at which we check the corresponding field supplied in the struct, is the type associated to that field name in general, evaluated at the supplied parameters and at "the term itself".  We don't have the whole term available while typechecking, of course, but we can build a version of it that contains all the previously typechecked fields, which is all we need for a well-typed record.  So we iterate through the fields (in the order specified in the *type*, since that determines the dependencies) while also accumulating the previously typechecked and evaluated fields.  At the end, we throw away the evaluated fields (although as usual, that seems wasteful).  Note that check_fields returns a modified version of the *user* fields 'tms', since it may need to resolve positional fields to named ones. *)
  let tms, ctms =
    check_fields status eta ctx ty m mn codata_args
      (* We convert the backwards alist of fields and types into a forwards list, for forwards recursion.  This should contain each field name only once, even for higher fields, since it comes from the codatatype where all the instances of a higher field are grouped into a pbijmap. *)
      (Bwd.to_list fields)
      tyargs
      (Abwd.map (fun (cube, { value; loc }) -> (cube, { value = Some value; loc })) tms)
      Emp Emp Emp in
  (* We had to typecheck the fields in the order given in the record type, since later ones might depend on earlier ones.  But then we re-order them back to the order given in the struct, to match what the user wrote. *)
  let fields, errs =
    Bwd.fold_left
      (fun (fields, errs) -> function
        (* If the term is still there, or if there are any remaining unlabeled fields, they are extra. *)
        | Some fldins, (_, { value = Some _; loc = tmloc }) ->
            (fields, Snoc (errs, diagnostic ?loc:tmloc (extra_field_in_struct eta fldins)))
        | None, (_, tm) -> (fields, Snoc (errs, diagnostic ?loc:tm.loc (Extra_field_in_tuple None)))
        | Some (fld, _), (_, { value = None; loc = tmloc }) -> (
            (* In the case of higher fields, the same field name will appear more than once in tms, but it will appear only once in the returned ctms; thus we take it only if it hasn't already been taken. *)
            match
              ( Term.StructfieldAbwd.find_string_opt fields fld,
                Term.StructfieldAbwd.find_string_opt ctms fld )
            with
            | Some _, _ -> (fields, errs)
            | None, Some x -> (Snoc (fields, x), errs)
            | None, None ->
                fatal ?loc:tmloc (Anomaly "taken raw field didn't end up in checked fields")))
      (Emp, Emp) tms in
  match errs with
  | Emp -> Term.Struct { eta; dim = m; fields; energy = energy status }
  | Snoc _ -> fatal (Accumulated ("check_struct", errs))

and check_fields : type mode a b c d s m n mn et.
    (mode, b, s) status ->
    (s, et) eta ->
    (mode, a, b) Ctx.t ->
    (* As before, the type, its substitution dimension, its Gel dimension, and its arguments *)
    (mode, kinetic) value ->
    m D.t ->
    (m, n, mn) D.plus ->
    (mode, m, n, d, c, et) codata_args ->
    (* The fields from the codatatype, to be checked against *)
    (mode * c * n * et) Term.CodatafieldAbwd.entry list ->
    (D.zero, mn, mn, mode normal) TubeOf.t ->
    (* The fields supplied by the user *)
    ((string * string list) option, [ `Normal | `Cube ] located * a check option located) Abwd.t ->
    (* The fields we have checked so far *)
    (mode * (m * b * s * et)) Term.StructfieldAbwd.t ->
    (* Evaluated versions of the fields we have checked so far *)
    (mode * m * s * et) Value.StructfieldAbwd.t ->
    (* Errors we have accumulated so far *)
    Code.t Asai.Diagnostic.t Bwd.t ->
    ((string * string list) option, [ `Normal | `Cube ] located * a check option located) Abwd.t
    * (mode * (m * b * s * et)) Term.StructfieldAbwd.t =
 fun status eta ctx ty m mn codata_args fields tyargs tms ctms etms errs ->
  (* Build a temporary value-struct consisting of the so-far checked and evaluated fields.  The insertion on a struct being checked is the identity, but it stores the substitution dimension of the type being checked against.  If this is a higher-dimensional record (e.g. Gel), there could be a nontrivial right dimension being trivially inserted, but that will get added automatically by an appropriate symmetry action if it happens. *)
  let str = Value.Struct { fields = etms; ins = ins_zero m; energy = energy status; eta } in
  match (fields, status) with
  | [], _ -> (
      (* If there are no more fields to check, we return.  We have accumulated a Bwd of errors as we progress through the fields, allowing later fields to typecheck (and, more importantly, produce their own meaningful error messages) even if earlier fields already failed.  Then at the end, if there are any such errors, we raise them all together.  *)
      match errs with
      | Emp -> (tms, ctms)
      | Snoc _ -> fatal (Accumulated ("check_struct", errs)))
  | Entry (fld, cdf) :: fields, Potential (name, args, hyp) ->
      (* Temporarily bind the current constant to the up-until-now value (or an error, if any have occurred yet), for (co)recursive purposes.  Note that this means as soon as one field fails, no other fields can be typechecked if they depend *at all* on earlier ones, even ones that didn't fail.  This could be improved in the future. *)
      run_with_definition name
        (hyp (Term.Struct { eta; dim = m; fields = ctms; energy = energy status }))
        errs
      @@ fun () ->
      (* The insertion on the *constant* being checked, by contrast, is always zero, since the constant is not nontrivially substituted at all yet. *)
      let head = head_of_potential name in
      (* The up-until-now term is also maybe an error. *)
      let prev_etm =
        unless_error (Neu { head; args; value = ready (Val str); ty = Lazy.from_val ty }) errs in
      check_field status eta ctx ty m mn codata_args fields tyargs fld cdf prev_etm tms ctms etms
        errs
  | Entry (fld, cdf) :: fields, Kinetic _ ->
      let prev_etm = unless_error str errs in
      check_field status eta ctx ty m mn codata_args fields tyargs fld cdf prev_etm tms ctms etms
        errs

and check_field : type mode a b c d s m n mn i et.
    (mode, b, s) status ->
    (s, et) eta ->
    (mode, a, b) Ctx.t ->
    (* As before, the type, its dimensions, and its arguments *)
    (mode, kinetic) value ->
    m D.t ->
    (m, n, mn) D.plus ->
    (mode, m, n, d, c, et) codata_args ->
    (mode * c * n * et) Term.CodatafieldAbwd.entry list ->
    (D.zero, mn, mn, mode normal) TubeOf.t ->
    (* The field being checked, by name and by data from the codatatype *)
    i Field.t ->
    (i, mode * c * n * et) Term.Codatafield.t ->
    (* The up-until-now term being checked *)
    ((mode, kinetic) value, Code.t) Result.t ->
    (* As before, user terms, checked terms, value terms, and errors *)
    ((string * string list) option, [ `Normal | `Cube ] located * a check option located) Abwd.t ->
    (mode * (m * b * s * et)) Term.StructfieldAbwd.t ->
    (mode * m * s * et) Value.StructfieldAbwd.t ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    ((string * string list) option, [ `Normal | `Cube ] located * a check option located) Abwd.t
    * (mode * (m * b * s * et)) Term.StructfieldAbwd.t =
 fun status eta ctx ty m mn ({ env; termctx; _ } as codata_args) fields tyargs fld cdf prev_etm tms
     ctms etms errs ->
  match (cdf, status, eta, termctx) with
  | ( Lower
        (type f g gmode ag)
        ((adj, fld_plus_lock, fldty) :
          (mode, f, g, gmode) Modalcell.adjunction
          * ((c, (mode id, n) dim_entry) snoc, mode, g, gmode, ag) plus_lock
          * (gmode, ag, kinetic) term),
      _,
      _,
      _ ) -> (
      let (Adjunction { left; right; _ }) = adj in
      (* A modal field whose (left adjoint) modality is nonparametric disappears at a dimension it filters nontrivially: it must be omitted from the tuple/comatch (an explicit occurrence is an error) and we skip it.  Otherwise its filter at the result dimension m is trivial and we check it normally. *)
      let (Has_filter left_filter) = Modality.filter left m in
      match Modality.filter_is_trivial m left_filter with
      | None ->
          let key = Some (Field.to_string fld, []) in
          let tms, errs =
            match
              Abwd.find_opt_and_update key key (fun (cube, x) -> (cube, locate_opt x.loc None)) tms
            with
            | Some ((_, { value = Some _; loc }), tms) ->
                ( tms,
                  Snoc
                    ( errs,
                      diagnostic ?loc (Extra_filtered_field_in_tuple (Field.to_string fld, left)) )
                )
            | Some ((_, { value = None; _ }), _) -> fatal (Anomaly "accessing same field twice")
            | None -> (tms, errs) in
          check_fields status eta ctx ty m mn codata_args fields tyargs tms ctms etms errs
      | Some Eq ->
          let ins = ins_zero m in
          (* The component of a modal field is checked in the context locked by the right adjoint of the field's adjunction (which is trivial for ordinary fields). *)
          let (Locked
                 (type bl)
                 ((ctx_plus_lock, lctx) : (b, mode, g, gmode, bl) plus_lock * (gmode, a, bl) Ctx.t))
              =
            Ctx.lock ctx right in
          let mkstatus lbl : (mode, b, s) status -> (gmode, bl, s) status = function
            | Kinetic l -> Kinetic l
            | Potential (c, args, hyp) ->
                let args = Value.Field (args, left_filter, fld, D.plus_zero m, ins) in
                let hyp tm =
                  let ctms =
                    Snoc
                      ( ctms,
                        Term.StructfieldAbwd.Entry
                          (fld, Term.Structfield.Lower (adj, ctx_plus_lock, tm, lbl)) ) in
                  hyp (Term.Struct { eta; dim = m; fields = ctms; energy = energy status }) in
                Potential (c, args, hyp) in
          let key = Some (Field.to_string fld, []) in
          let tm, tms, lbl =
            match
              Abwd.find_opt_and_update key key (fun (cube, x) -> (cube, locate_opt x.loc None)) tms
            with
            | Some ((cube, { value = Some tm; loc }), tms) ->
                (match (cube.value, D.compare_zero m) with
                | `Cube, Zero -> fatal ?loc:cube.loc (Zero_dimensional_cube_abstraction "comatch")
                | _ -> ());
                ({ value = tm; loc }, tms, `Labeled)
            | Some ((_, { value = None; _ }), _) -> fatal (Anomaly "accessing same field twice")
            | None -> (
                match
                  Abwd.find_opt_and_update None key
                    (fun (cube, x) -> (cube, locate_opt x.loc None))
                    tms
                with
                | Some ((cube, { value = Some tm; loc }), tms) ->
                    (match (cube.value, D.compare_zero m) with
                    | `Cube, Zero ->
                        fatal ?loc:cube.loc (Zero_dimensional_cube_abstraction "comatch")
                    | _ -> ());
                    ({ value = tm; loc }, tms, `Unlabeled)
                | Some ((_, { value = None; _ }), _) -> fatal (Anomaly "accessing same field twice")
                | None -> fatal (missing_field_in_struct eta fld)) in
          let etms, ctms, errs =
            (* We trap any errors produced by 'check', adding them instead to the list of accumulated errors and going on.  Note that if any previous fields that have already failed, then prev_etm will be bound to an error value, and so if the type of this field depends on the value of any previous one, tyof_field will raise that error, which we catch and add to the list; but it will be (Accumulated Emp) so it won't be displayed to the user. *)
            Reporter.try_with ~fatal:(fun e -> (etms, ctms, Snoc (errs, e))) @@ fun () ->
            (* We don't need the error-checking of tyof_field, since we are getting our fields directly from the codatatype definition and so we already know that they have the right dimensions.  So we can call directly into the helper function tyof_lower_codatafield.  Note that we pass it prev_etm, env, and tyargs that consist of values in the old context, but the return value ety is in the new degenerated context. *)
            let ety =
              tyof_lower_codatafield prev_etm fld adj fld_plus_lock fldty env tyargs m mn
                ~key:`Nokey in
            let ctm = check (mkstatus lbl status) lctx tm ety in
            let etms =
              Snoc
                ( etms,
                  Value.StructfieldAbwd.Entry
                    (fld, Value.Structfield.Lower (adj, lazy_eval (Ctx.env lctx) ctm, lbl)) ) in
            let ctms =
              Snoc
                ( ctms,
                  Term.StructfieldAbwd.Entry
                    (fld, Term.Structfield.Lower (adj, ctx_plus_lock, ctm, lbl)) ) in
            (etms, ctms, errs) in
          check_fields status eta ctx ty m mn codata_args fields tyargs tms ctms etms errs)
  | Higher (ic0, fldty), Potential _, Noeta, (lazy (Some termctx)) ->
      let Eq = D.plus_uniq mn (D.plus_zero m) in
      let i = Field.dim fld in
      check_higher_field status ctx ty m i codata_args fields termctx tyargs tms ctms etms errs fld
        (PlusPbijmap.build m i { build = (fun _ -> None) })
        (InsmapOf.build m i { build = (fun _ -> None) })
        (all_pbij_between m i) prev_etm ic0 fldty
  | Higher _, Potential _, _, (lazy None) ->
      fatal (Anomaly "missing termctx in codatatype with higher fields")
  | Higher _, Kinetic _, _, _ -> .

and check_higher_field : type mode a b c d m i ic0.
    (mode, b, potential) status ->
    (mode, a, b) Ctx.t ->
    (* Type being checked against and its data *)
    (mode, kinetic) value ->
    (* m = substitution dimension, i = intrinsic dimension *)
    m D.t ->
    i D.t ->
    (mode, m, D.zero, d, c, no_eta) codata_args ->
    (mode * c * D.zero * no_eta) Term.CodatafieldAbwd.entry list ->
    (mode, d, (c, (mode id, D.zero) dim_entry) snoc) termctx ->
    (D.zero, m, m, mode normal) TubeOf.t ->
    (* As before, user terms, checked terms, value terms, and errors *)
    ((string * string list) option, [ `Normal | `Cube ] located * a check option located) Abwd.t ->
    (mode * (m * b * potential * no_eta)) Term.StructfieldAbwd.t ->
    (mode * m * potential * no_eta) Value.StructfieldAbwd.t ->
    Code.t Asai.Diagnostic.t Bwd.t ->
    (* Field being checked *)
    i Field.t ->
    (* Values of this field checked so far, as terms *)
    (m, i, mode * b) PlusPbijmap.t ->
    (* Evaluated versions of those of them that are insertions (hence can be used) *)
    (m, i, (mode, potential) lazy_eval option) InsmapOf.t ->
    (* Remaining pbijs to check *)
    (m, i) pbij_between Seq.t ->
    (* Term-up-until-now *)
    ((mode, kinetic) value, Code.t) Result.t ->
    (* The unevaluated type of the current field being checked. *)
    (i, (c, (mode id, D.zero) dim_entry) snoc, ic0, mode) plusmap ->
    (mode, ic0, kinetic) term ->
    ((string * string list) option, [ `Normal | `Cube ] located * a check option located) Abwd.t
    * (mode * (m * b * potential * no_eta)) Term.StructfieldAbwd.t =
 fun status ctx ty m intrinsic ({ env; _ } as codata_args) fields termctx tyargs tms ctms etms errs
     fld cvals evals pbijs prev_etm ic0 fldty ->
  (* We recurse through all the partial bijections that could be associated to this field name. *)
  match Seq.uncons pbijs with
  | Some
      ( Pbij_between
          (type r)
          (Pbij (type s h) ((fldins, fldshuf) : (m, s, h) insertion * (r, h, i) shuffle) as pbij :
            (m, i, r) pbij),
        pbijs ) ->
      (* Degenerate the context by the number of remaining dimensions for this partial bijection *)
      let r = remaining pbij in
      let (Degctx
             (type rb)
             ((plusmap, degctx, degenv) :
               (r, b, rb, mode) plusmap * (mode, a, rb) Ctx.t * (mode, r, b) env)) =
        degctx ctx r in
      (* To make a new status, the arguments need to be eval-readbacked into degctx, and for that to make sense the head needs to be higher-dimensional also. *)
      let newstatus : (mode, rb, potential) status =
        match status with
        | Potential
            (type hm aa any)
            ((head, args, hyp) :
              (hm, aa) potential_head
              * (hm, mode, any) apps
              * ((mode, b, potential) term -> (hm, aa, potential) term)) ->
            (* We eval-readback the args to raise them to degctx.  We also increase the dimension of the potential_head; this happens at the bottom of the spine recursion, where the accumulated locks from any modal field projections put the contexts at the head's mode. *)
            let rec erapps : type m2 any2 x2 z2.
                (m2, x2, z2) Ctx.t ->
                (m2, r, z2) env ->
                (hm, m2, any2) apps ->
                (hm, aa) potential_head * (hm, m2, any2) apps =
             fun ctx degenv -> function
               | Emp ->
                   let (head : (hm, aa) potential_head) =
                     match head with
                     | Constant (c, cmode, n) ->
                         let (Plus rn) = D.plus n in
                         Constant (c, cmode, D.plus_out r rn)
                     | Meta (meta, metaenv) ->
                         let (Plus rn) = D.plus (dim_env metaenv) in
                         let d = Global.find_meta meta in
                         (* In the case of a metavariable, we eval-readback its stored environment to raise it to degctx. *)
                         Meta (meta, eval_env degenv rn (readback_env ctx metaenv d.termctx)) in
                   (head, Emp)
               | Field (apps, filter, fldname, nk, appins) ->
                   let fm = Modality.filter_modality filter in
                   let n = cod_left_ins appins in
                   let (Plus rn) = D.plus n in
                   let (Plus rn_k) = D.plus (D.plus_right nk) in
                   let (Plus r_nz) = D.plus (dom_ins appins) in
                   let newins = plus_ins r r_nz rn appins in
                   (* The result dimension of the projection is raised by r, so we recompute the field's filter at the new (outer) result dimension; the inner spine is raised correspondingly.  MODALTODO: for a nonparametric field this raising can interact nontrivially with the filter (only reachable with modal higher fields, which are unimplemented). *)
                   let (Has_filter newfilter) = Modality.filter fm (cod_left_ins newins) in
                   (* The spine inside a modal field projection lives behind a lock by the left adjoint. *)
                   let (Locked (plus, lctx)) = Ctx.lock ctx fm in
                   let ldegenv = key_env degenv (Modalcell.id fm) plus in
                   let head, newapps = erapps lctx ldegenv apps in
                   (head, Value.Field (newapps, newfilter, fldname, rn_k, newins))
               | Arg
                   (type dom modality any' n m mz z)
                   ((apps, filter_nm, arg, appins) :
                     (hm, m2, any') apps
                     * (dom, modality, m2, n, m) Modality.filter_dim
                     * (n, dom normal) CubeOf.t
                     * (mz, m, z) insertion) ->
                   let n = CubeOf.dim arg in
                   let m = cod_left_ins appins in
                   let (Plus rm) = D.plus m in
                   let (Plus r_mz) = D.plus (dom_ins appins) in
                   let newins = plus_ins r r_mz rm appins in
                   let modality = Modality.filter_modality filter_nm in
                   let (Has_filter filter_sr) = Modality.filter modality r in
                   let s = Modality.filtered r filter_sr in
                   let (Plus sn) = D.plus n in
                   let filter_sn_rm = Modality.filter_plus sn rm filter_sr filter_nm in
                   (* First we readback the terms and types. *)
                   let (Locked (plus, lctx)) = Ctx.lock ctx modality in
                   let [ tms; tys ] =
                     CubeOf.pmap
                       { map = (fun _ [ x ] -> [ readback_nf lctx x; readback_val lctx x.ty ]) }
                       [ arg ] (Cons (Cons Nil)) in
                   let ldegenv = key_env degenv (Modalcell.id modality) plus in
                   (* Now we evaluate them in degenv to increase the dimension.  *)
                   let sldegenv =
                     act_env ldegenv (opt_op_of_opt_sface (Modality.sface_of_filter r filter_sr))
                   in
                   let etms = eval_args sldegenv sn (D.plus_out s sn) tms in
                   let etys = eval_args sldegenv sn (D.plus_out s sn) tys in
                   (* Now we have to reassociate the terms with the types to make a new cube of normals.  This is like norm_of_vals_cube, except that the types are already instantiated to dimension n, and we have only to instantiate them the rest of the way at dimension r. *)
                   let new_tm_tbl = Hashtbl.create 10 in
                   let newarg =
                     CubeOf.mmap
                       {
                         map =
                           (fun fab [ tm; ty ] ->
                             let (SFace_of_plus (ml, fa, fb)) = sface_of_plus sn fab in
                             let instargs =
                               TubeOf.build D.zero
                                 (D.zero_plus (dom_sface fa))
                                 {
                                   build =
                                     (fun fc ->
                                       let (Plus kl) = D.plus (D.plus_right ml) in
                                       Hashtbl.find new_tm_tbl
                                         (SFace_of
                                            (sface_plus_sface
                                               (comp_sface fa (sface_of_tface fc))
                                               sn kl fb)));
                                 } in
                             let ty = inst ty instargs in
                             let newtm = { tm; ty } in
                             Hashtbl.add new_tm_tbl (SFace_of fab) newtm;
                             newtm);
                       }
                       [ etms; etys ] in
                   let head, newapps = erapps ctx degenv apps in
                   (head, Arg (newapps, filter_sn_rm, newarg, newins))
               | Inst _ -> fatal (Anomaly "inst in eval-readback when checking higher field") in
            let head, args = erapps ctx degenv args in
            let (Plus ni) = D.plus intrinsic in
            (* We add the current field projection to the args, with an insertion obtained by incorporating the remaining dimensions into the evaluation. *)
            let (Plus rm) = D.plus m in
            let newins = ins_plus_of_pbij fldins fldshuf rm in
            (* Higher fields are never modal, so the projecting modality is the identity and its filter (at the result dimension) is trivial. *)
            let (Has_filter idfilter) =
              Modality.filter (Modality.id (Ctx.mode ctx)) (cod_left_ins newins) in
            let args = Value.Field (args, idfilter, fld, ni, newins) in
            (* To hypothesize a value for the current term, we insert the supposed value as the value of this field.  Note the context rb of the supposed value is the degenerated rb instead of the original b, but this is exactly right for the value that's supposed to go in at this pbij.  *)
            let hyp (tm : (mode, rb, potential) term) : (hm, aa, potential) term =
              let hsf =
                Term.Structfield.Higher (PlusPbijmap.set pbij (Some (PlusFam (plusmap, tm))) cvals)
              in
              let ctms = Snoc (ctms, Entry (fld, hsf)) in
              hyp (Term.Struct { eta = Noeta; dim = m; fields = ctms; energy = energy status })
            in
            Potential (head, args, hyp) in
      (* Get the user's supplied term for this partial bijection *)
      let key = Some (Field.to_string fld, strings_of_pbij pbij) in
      let tm, tms =
        match
          Abwd.find_opt_and_update key key (fun (cube, x) -> (cube, locate_opt x.loc None)) tms
        with
        | Some ((cube, { value = Some tm; loc }), tms) ->
            (match (cube.value, D.compare_zero m) with
            | `Cube, Zero -> fatal ?loc:cube.loc (Zero_dimensional_cube_abstraction "comatch")
            | _ -> ());
            ({ value = tm; loc }, tms)
        | Some ((_, { value = None; _ }), _) -> fatal (Anomaly "accessing same method twice")
        (* Higher fields cannot be positional *)
        | None -> fatal (Missing_method_in_comatch (fld, Some pbij)) in
      let evals, cvals, errs =
        (* Go into the location of the field right away, so that errors in dimension calculations will be labeled by the right field. *)
        with_loc tm.loc @@ fun () ->
        (* We trap any errors produced by 'tyof_field' or 'check', adding them instead to the list of accumulated errors and going on.  Note that if any previous fields that have already failed, then prev_etm will be bound to an error value, and so if the type of this field depends on the value of any previous one, tyof_field will raise that error, which we catch and add to the list; but it will be (Accumulated Emp) so it won't be displayed to the user. *)
        Reporter.try_with ~fatal:(fun e -> (evals, cvals, Snoc (errs, e))) @@ fun () ->
        let shuf : (mode, r, h, i, c) Norm.shuffleable =
          Nontrivial
            {
              dbwd = length_env env;
              shuffle = fldshuf;
              deg_env = (fun _sh r_sh e -> eval_env degenv r_sh (readback_env ctx e termctx));
              deg_nf =
                (fun nf ->
                  let ctm = readback_nf ctx nf in
                  let tm = eval_term degenv ctm in
                  let cty = readback_val ctx nf.ty in
                  let ity = eval_term degenv cty in
                  let argstbl = Hashtbl.create 10 in
                  let tyargs =
                    TubeOf.build D.zero (D.zero_plus r)
                      {
                        build =
                          (fun fa ->
                            let faenv = act_env degenv (opt_op_of_sface (sface_of_tface fa)) in
                            let fatm = eval_term faenv ctm in
                            let faty =
                              inst (eval_term faenv cty)
                                (TubeOf.build D.zero
                                   (D.zero_plus (dom_tface fa))
                                   {
                                     build =
                                       (fun fb ->
                                         Hashtbl.find argstbl
                                           (SFace_of
                                              (comp_sface (sface_of_tface fa) (sface_of_tface fb))));
                                   }) in
                            let nf = { tm = fatm; ty = faty } in
                            Hashtbl.add argstbl (SFace_of (sface_of_tface fa)) nf;
                            nf);
                      } in
                  { tm; ty = inst ity tyargs });
            } in
        (* Evaluate the type for this instance of the field, and check the user's term against it. *)
        let ety = tyof_higher_codatafield prev_etm fld env tyargs fldins ic0 fldty ~shuf in
        let ctm = check newstatus degctx tm ety in
        (* Add the typechecked term to the list *)
        let cvals = PlusPbijmap.set pbij (Some (PlusFam (plusmap, ctm))) cvals in
        (* If there are no remaining dimensions, we can evaluate the term and add it to the list of evaluated fields. *)
        let evals =
          match D.compare_zero r with
          | Pos _ -> evals
          | Zero ->
              let Eq = eq_of_zero_shuffle fldshuf in
              InsmapOf.set fldins (Some (lazy_eval (Ctx.env degctx) ctm)) evals in
        (evals, cvals, errs) in
      check_higher_field status ctx ty m intrinsic codata_args fields termctx tyargs tms ctms etms
        errs fld cvals evals pbijs prev_etm ic0 fldty
  | None ->
      let plusdim = D.zero_plus m in
      let env = Ctx.env ctx in
      let deg = id_deg (D.plus_out (dim_env env) plusdim) in
      let etms =
        Snoc
          ( etms,
            Entry (fld, Higher (lazy { vals = evals; intrinsic; plusdim; env; deg; terms = cvals }))
          ) in
      let ctms = Snoc (ctms, Entry (fld, Higher cvals)) in
      check_fields status Noeta ctx ty m (D.plus_zero m) codata_args fields tyargs tms ctms etms
        errs

and synth : type mode a b s.
    ?nosynth:Code.t Asai.Diagnostic.t ->
    (mode, b, s) status ->
    (mode, a, b) Ctx.t ->
    a synth located ->
    (mode, b, s) term * (mode, kinetic) value =
 fun ?nosynth status ctx tm ->
  let mode = Ctx.mode ctx in
  let go () =
    match (tm.value, status) with
    | Var i, _ -> (
        (* We look up the raw variable index in the context.  This returns its De Bruijn level (which we don't need), its value, its annotating modality, and the information that goes into its De Bruijn index (insertion and plus_with_locks). *)
        let (Lookup { result; value; dirt; modality; filter; insert; plus = plus_tgt }) =
          Ctx.lookup ctx i in
        (* If this is a let-bound variable whose value contains occurrences of currently-being-defined constants, record that for any active occurrence-analysis scope. *)
        Positivity.record dirt;
        (* We extract the composite locking modality. *)
        let (Any_ctx ctx) = Ctx.remove_locks ctx plus_tgt in
        let (Plus_with_locks (_, locks)) = plus_tgt in
        let lock = Locks.cod locks in
        (* To produce its term as a variable (or illusory field access) we have to replace the lock-containing context by a single lock by its annotating modality. *)
        let (Has_plus_lock plus_src) = plus_lock modality in
        let tm, ty =
          match result with
          | `Var (_, fa) ->
              ( Term.Var (Index (insert, fa, filter, plus_with_locks_of_plus_lock plus_src)),
                value.ty )
          | `Field (_, field) ->
              (* TODO: Double-check that this zero is correct *)
              let ins = ins_zero D.zero in
              (* Illusory field-access variables always refer to the top face.  They are used only for record fields, which are never modal, so the projecting modality is the identity. *)
              let (Inserted (n, _)) = inserted insert (Ctx.tctx ctx) in
              (* The self-variable and its field projection live at the variable's own mode (its annotating modality's source); the ambient Key later transports to the context mode. *)
              let dmode = Modality.src modality in
              ( Term.Field
                  ( modal_id dmode
                      (Var
                         (Index (insert, id_sface n, filter, plus_with_locks_of_plus_lock plus_src))),
                    field,
                    ins ),
                tyof_field (Modality.id dmode) (Ok value.tm) value.ty field ~shuf:Trivial ins )
        in
        (* Any keys supplied explicitly by the user have been stripped off already, but we can insert an identity key or a unique key as well. *)
        match (Modality.compare modality lock, Modalcell.find_unique modality lock) with
        | Eq, _ ->
            (* If the two modalities are equal, we still technically need an "identity key" substitution to replace the lock-containing context with a lock-only context. *)
            ( realize status
                (Term.Key { tm; cell = Modalcell.id modality; plus_tgt; plus_src }
                  : (mode, b, kinetic) term),
              (act_value ty (id_deg D.zero) (Modalcell.id2 mode) : (mode, kinetic) value) )
        | _, Some (Unique cell) ->
            (* And if the key is unique, we act by that key. *)
            ( realize status (Term.Key { tm; cell; plus_tgt; plus_src }),
              act_value ty (id_deg D.zero) cell )
        | Neq, None ->
            (* If the modalities are not equal, and the key is not unique, then the user should have given an explicit key. *)
            fatal (Missing_key (modality, lock)))
    | Const name, _ -> (
        (* If this is one of the constants currently being defined, record the occurrence for any active occurrence-analysis scope (e.g. the argument telescope of a datatype constructor, or the value of a let binding). *)
        Positivity.record_const name;
        let (Definition { mode; ty; parametric; _ }) = Global.find name in
        match Modal.Mode.compare mode (Ctx.mode ctx) with
        | Eq ->
            (match (parametric, Ctx.parametric_locked ctx) with
            (* If the context is locked, then nonparametric constants are not allowed.  *)
            | `Nonparametric, true -> fatal (Locked_constant (PConstant name))
            (* Thus, if one of the currently-being-defined constants is encountered in a locked context, they *must* be parametric. *)
            | `Maybe_parametric, true -> Global.set_parametric name
            (* On the other hand, if the context is not locked and we encounter a nonparametric constant, then the current constants must be nonparametric.  (The Global.set functions handle checking for conflicts between requirements of parametricness of the current definitions.) *)
            | `Nonparametric, false -> Global.set_nonparametric (Some name)
            | _ -> ());
            (realize status (Const name), eval_term (Emp (mode, D.zero)) ty)
        | Neq -> fatal (Mode_mismatch (`User, "synthesizing constant", mode, None, Ctx.mode ctx)))
    | Field (tm, fld, lock), _ -> (
        (* To take a field of something, the type of the something must be a record-type that contains such a field, possibly substituted to a higher dimension and instantiated.  For a modal field the term is synthesized in a context locked by the left adjoint of the field's adjunction, which the user must specify (since we don't yet know the field's adjunction, different types could reuse the field name).  An unannotated projection uses the identity modality. *)
        (* tyof_field_withname verifies that fm is the left adjoint of the field's adjunction, so the resulting type is keyed by the counit into the ambient context. *)
        let synth_field : type dom f. (dom, f, mode) Modality.t -> _ =
         fun fm ->
          let (Locked (plus_lock, lctx)) = Ctx.lock ctx fm in
          let stm, sty = synth (Kinetic `Nolet) lctx tm in
          let etm = eval_term (Ctx.env lctx) stm in
          let WithIns (fld, ins), newty = tyof_field_withname fm lctx (Ok etm) sty fld in
          (realize status (Field (Modal (fm, plus_lock, stm), fld, ins)), newty) in
        match lock with
        | None -> synth_field (Modality.id (Ctx.mode ctx))
        | Some lockname -> (
            match Modality.of_name_tgt (Ctx.mode ctx) lockname.value with
            | Error e -> modality_fatal "field projection locking annotation" (e :> modality_error)
            | Ok (Wrap fm) -> synth_field fm))
    | UU umode, _ -> (
        match Modal.Mode.compare umode mode with
        | Eq -> (realize status (Term.UU (mode, D.zero)), universe mode D.zero)
        | Neq -> fatal (Mode_mismatch (`User, "synthesizing universe", umode, None, mode)))
    | Pi (x, modality, dom, cod), _ -> (
        match Modality.of_name_tgt mode modality.value with
        | Error e -> modality_fatal "synthesizing pi-type" (e :> modality_error)
        | Ok (Wrap modality) ->
            if not (Modality.tangible modality) then fatal (Intangible_modality modality);
            let (Locked (plus, lctx)) = Ctx.lock ctx modality in
            (* These user-level pi-types are always dimension zero, so the domain must be a zero-dimensional type. *)
            let cdom = check (Kinetic `Nolet) lctx dom (universe (Modality.src modality) D.zero) in
            let edom = eval_term (Ctx.env lctx) cdom in
            let ccod =
              check (Kinetic `Nolet) (Ctx.ext ctx modality x edom) cod (universe mode D.zero) in
            ( realize status
                (pi
                   (singleton_variables D.zero (View.hinted x edom))
                   (Modal (modality, plus, cdom))
                   ccod),
              universe mode D.zero ))
    | HigherPi (x, modality, dom, cod), _ -> (
        match Modality.of_name_tgt mode modality.value with
        | Error e -> modality_fatal "synthesizing higher pi-type" (e :> modality_error)
        | Ok (Wrap (type dom modality) (modality : (dom, modality, mode) Modality.t)) -> (
            let (Locked (plus, lctx)) = Ctx.lock ctx modality in
            let cdom, domty = synth (Kinetic `Nolet) lctx dom in
            let edom = eval_term (Ctx.env lctx) cdom in
            match view_type domty "higher pi domain" with
            | Canonical
                (type hmode m k km)
                ((_, UU (_dmode, k), ins, edoms) :
                  hmode head
                  * (dom, k, m) canonical
                  * (km, k, m) insertion
                  * (D.zero, km, km, dom normal) TubeOf.t) -> (
                let Eq = eq_of_ins_zero ins in
                (* The dimension k of the domain is the *filtered* dimension of the pi-type.  In particular, since filtering is idempotent, k must itself be stable under filtering by the modality. *)
                let (Has_filter kfilter) = Modality.filter modality k in
                match D.compare (Modality.filtered k kfilter) k with
                | Neq -> fatal (Invalid_higher_function "domain dimension is not modally filtered")
                | Eq -> (
                    let cdomt =
                      TubeOf.mmap { map = (fun _ [ x ] -> readback_nf lctx x) } [ edoms ] in
                    let cdoms = TubeOf.plus_cube cdomt (CubeOf.singleton cdom) in
                    let edomt = TubeOf.mmap { map = (fun _ [ x ] -> x.tm) } [ edoms ] in
                    let edoms = TubeOf.plus_cube edomt (CubeOf.singleton edom) in
                    let _, binds = dom_vars ctx modality edoms in
                    let newctx = Ctx.cube_vis ctx kfilter x binds in
                    let ccod, codty = synth (Kinetic `Nolet) newctx cod in
                    match view_type codty "higher pi codomain" with
                    | Canonical
                        (type hmode n2 m2 nm2)
                        ((_, UU (codmode, n), ins', ecodt) :
                          hmode head
                          * (mode, n2, m2) canonical
                          * (nm2, n2, m2) insertion
                          * (D.zero, nm2, nm2, mode normal) TubeOf.t) -> (
                        let Eq = eq_of_ins_zero ins' in
                        (* The dimension n of the codomain is the outer (unfiltered) dimension of the pi-type: its filtering must be the domain dimension k. *)
                        let (Has_filter nfilter) = Modality.filter modality n in
                        match
                          ( D.compare (Modality.filtered n nfilter) k,
                            Modal.Mode.compare codmode mode )
                        with
                        | Neq, _ ->
                            fatal (Invalid_higher_function "invalid single codomain dimension")
                        | _, Neq ->
                            fatal (Mode_mismatch (`User, "higher pi codomain", codmode, None, mode))
                        | Eq, Eq ->
                            let ccods =
                              let build : type j.
                                  (j, n2) sface -> (j, dom * modality * mode * b) CodFam.t =
                               fun s ->
                                match pface_of_sface s with
                                | `Id Eq -> Cod (nfilter, ccod)
                                | `Proper t ->
                                    let (Filter_sface (fb, sfilter)) =
                                      Modality.filter_sface nfilter s in
                                    let sctx =
                                      Ctx.cube_vis ctx
                                        (Modality.filter_idempotent sfilter)
                                        x (CubeOf.subcube fb binds) in
                                    Cod (sfilter, readback_nf sctx (TubeOf.find ecodt t)) in
                              CodCube.build n { build } in
                            let tyargstbl = Hashtbl.create 10 in
                            let tyargs =
                              TubeOf.build D.zero (D.zero_plus n)
                                {
                                  build =
                                    (fun t ->
                                      let j = dom_tface t in
                                      let t' = sface_of_tface t in
                                      let (Filter_sface (fb, tfilter)) =
                                        Modality.filter_sface nfilter t' in
                                      let ctm =
                                        Term.Pi
                                          {
                                            x =
                                              singleton_variables (dom_sface fb)
                                                (View.hinted x (CubeOf.find edoms fb));
                                            filter = tfilter;
                                            doms = Modal (modality, plus, CubeOf.subcube fb cdoms);
                                            cods = CodCube.subcube t' ccods;
                                          } in
                                      let tm = eval_term (Ctx.env ctx) ctm in
                                      let tyargs =
                                        TubeOf.build D.zero (D.zero_plus j)
                                          {
                                            build =
                                              (fun v ->
                                                Hashtbl.find tyargstbl
                                                  (Tface_of (tface_comp_sface t (sface_of_tface v))));
                                          } in
                                      let ty = inst (universe mode j) tyargs in
                                      let arg = { tm; ty } in
                                      Hashtbl.add tyargstbl (Tface_of t) arg;
                                      arg);
                                } in
                            ( realize status
                                (Pi
                                   {
                                     x = singleton_variables k (View.hinted x edom);
                                     filter = nfilter;
                                     doms = Modal (modality, plus, cdoms);
                                     cods = ccods;
                                   }),
                              inst (universe mode n) tyargs ))
                    | _ -> fatal (Invalid_higher_function "invalid single codomain")))
            | _ -> fatal (Invalid_higher_function "invalid single domain")))
    | ( InstHigherPi
          (type n nb an)
          ((n', doms, cod) : n D.pos * (a, nb, an) Raw.tel * an check located),
        _ ) -> (
        let modalities = Raw.mods_of_tel doms in
        let modality =
          List.fold_left
            (fun (m1 : mode Modality.src_wrapped option) m2 ->
              match (m1, Modality.of_name_tgt mode m2.value) with
              | _, Error e -> modality_fatal "synthesizing higher pi-type" (e :> modality_error)
              | None, Ok m -> Some m
              | Some (Wrap m1), Ok (Wrap m2) -> (
                  match Modality.compare m1 m2 with
                  | Eq -> Some (Wrap m1)
                  | Neq -> fatal (Modality_mismatch (`User, "synthesizing higher pi-type", m1, m2))))
            None modalities in
        match modality with
        | None -> fatal (Anomaly "no modality found when synthesizing higher pi-type")
        | Some (Wrap (type dom modality) (modality : (dom, modality, mode) Modality.t)) -> (
            let (Locked (plus, lctx)) = Ctx.lock ctx modality in
            (* The dimension annotating the arrow is the outer (unfiltered) dimension n.  We filter it by the modality to obtain the dimension k of the cube of domains. *)
            let n = D.pos n' in
            let (Has_filter (type kf) (nfilter : (dom, modality, mode, kf, n) Modality.filter_dim))
                =
              Modality.filter modality n in
            let k = Modality.filtered n nfilter in
            let kfilter = Modality.filter_idempotent nfilter in
            let domstbl = Hashtbl.create 10 in
            let varstbl = Hashtbl.create 10 in
            (* We check the domains by traversing the faces of the filtered dimension k, consuming entries of the raw telescope as we go and raising an error if there are too few.  The state of the traversal carries the current context along with a witness of its raw length and the remaining telescope, which keeps the raw indices of the telescope entries aligned with the context. *)
            let module S = struct
              type _ t =
                | State : {
                    xctx : (dom, 'ac, 'e) Ctx.t;
                    plus : (a, 'c, 'ac) N.plus;
                    tele : ('ac, 'r, an) Raw.tel;
                  }
                    -> 'c t
            end in
            let module Build = NICubeOf.Traverse (S) in
            let build : type left m.
                (m, kf) sface -> left S.t -> (left, m, binder_name) Build.fwrap_left =
             fun s (State { xctx; plus = ac; tele }) ->
              match tele with
              | Emp -> fatal (Not_enough_domains k)
              | Ext (x, _, dom, rest) -> (
                  let m = dom_sface s in
                  (* We check the domains against universe 0, since they should be fully instantiated. *)
                  let cdom =
                    check (Kinetic `Nolet) xctx dom (universe (Modality.src modality) D.zero) in
                  let edom = eval_term (Ctx.env xctx) cdom in
                  (* Further errors here should also be reported on the relevant domain term. *)
                  with_loc dom.loc @@ fun () : (left, m, binder_name) Build.fwrap_left ->
                  (* No_such_level indicates a readback failure, meaning that some domain or boundary was not defined in the correct context (e.g. used unavailable variables). *)
                  Reporter.try_with ~fatal:(fun d ->
                      match d.message with
                      | No_such_level _ ->
                          fatal ?loc:d.explanation.loc
                            (Invalid_higher_function "invalid domain scope")
                      | _ -> fatal_diagnostic d)
                  @@ fun () : (left, m, binder_name) Build.fwrap_left ->
                  let dom, tyargs =
                    match D.compare_zero m with
                    | Zero ->
                        ( readback_val lctx edom,
                          (TubeOf.empty D.zero : (D.zero, m, m, dom normal) TubeOf.t) )
                    (* If the dimension of this domain is supposed to be positive, the supplied domain must be fully instantiated by at least that dimension (perhaps more, since it could come from something higher-dimensional).  We pull off those instantiation arguments. *)
                    | Pos m -> (
                        match split_inst m (view_term edom) with
                        | Some (Head_apps (head, Any args), tyargs) ->
                            (* After spliting off those instantiation arguments, we read back the rest of the type in the *original* context, to make sure it makes sense there and yield the term domain. *)
                            (readback_neu lctx head args, tyargs)
                        | None -> fatal (Invalid_higher_function "invalid domain")) in
                  (* Then we check that the instantiation arguments we pulled off are each equal to the corresponding *variable* from the earlier domains. *)
                  TubeOf.miter
                    {
                      it =
                        (fun t [ arg ] ->
                          match
                            equal_nf xctx arg
                              (Hashtbl.find varstbl (SFace_of (comp_sface s (sface_of_tface t))))
                          with
                          | Ok () -> ()
                          | Error _ -> fatal (Invalid_higher_function "invalid domain boundary"));
                    }
                    [ tyargs ];
                  (* We "return" the domain term by adding it to a hashtbl. *)
                  Hashtbl.add domstbl (SFace_of s) dom;
                  (* I think we want the identity modalities here since this is temporary for adding a bunch of domains to the same context. *)
                  let idm = Modality.id (Ctx.mode xctx) in
                  let newctx = Ctx.ext xctx idm x edom in
                  (* We also get and store the normal corresponding to this variable, for checking the tyargs of later domains. *)
                  let (Lookup { value; modality; plus = Plus_with_locks (_, locks); _ }) =
                    Ctx.lookup newctx (Top, None) in
                  (* The modality and lock must be trivial since we just added it. *)
                  (match (Modality.compare_id modality, Modality.compare_id (Locks.cod locks)) with
                  | Eq, Eq -> Hashtbl.add varstbl (SFace_of s) value
                  | _ -> fatal (Anomaly "invalid modalities when checking InstHigherPi"));
                  Fwrap
                    ( NFamOf (View.hinted x edom),
                      State { xctx = newctx; plus = Suc ac; tele = rest } )) in
            (* We don't care about the produced context, since its checked length is wrong.  We want just one cube of variables, the total raw length added to the previous one, and the leftover telescope.  *)
            let (Wrap (xs, State { xctx = _; plus = af; tele = rest })) =
              Build.build_left k { build } (State { xctx = lctx; plus = Zero; tele = doms }) in
            match rest with
            | Ext (_, _, { loc; _ }, _) ->
                fatal ?loc (Invalid_higher_function "too many domains for the dimension")
            | Emp -> (
                (* Since the leftover telescope is empty, the raw context at its end, which is the context of the codomain, is equal to the current raw context. *)
                let cdoms =
                  CubeOf.build k { build = (fun s -> Hashtbl.find domstbl (SFace_of s)) } in
                let _, binds =
                  dom_vars ctx modality
                    (CubeOf.mmap { map = (fun _ [ x ] -> eval_term (Ctx.env lctx) x) } [ cdoms ])
                in
                let xsv = Variables (D.zero, D.zero_plus k, xs) in
                let newctx = Ctx.vis ctx kfilter D.zero (D.zero_plus k) xs binds af in
                (* We likewise check the codomain against universe 0. *)
                let ccod = check (Kinetic `Nolet) newctx cod (universe mode D.zero) in
                with_loc cod.loc @@ fun () ->
                Reporter.try_with ~fatal:(fun d ->
                    match d.message with
                    | No_such_level _ ->
                        fatal ?loc:d.explanation.loc
                          (Invalid_higher_function "invalid codomain scope")
                    | _ -> fatal_diagnostic d)
                @@ fun () ->
                (* It must also be fully instantiated at at least the total dimension. *)
                match split_inst n' (eval_term (Ctx.env newctx) ccod) with
                | None -> fatal (Invalid_higher_function "invalid codomain")
                | Some (Head_apps (head, Any args), tyargs) ->
                    (* After spliting off those instantiation arguments, we read back the rest of the type to yield the top-dimensional codomain. *)
                    let cod = readback_neu newctx head args in
                    (* To get the lower-dimensional codomains, and the instantation arguments of the whole pi-type, we iterate through the split-off tyargs. *)
                    let [ ecods; piargs ] =
                      let map : type m.
                          (m, D.zero, n, n) tface ->
                          (m, (mode normal, Tlist.nil) Tlist.cons) CubeOf.Heter.hft ->
                          ( m,
                            ( [ `Neu of mode head_apps | `Val of (mode, kinetic) value ],
                              ((mode, b, kinetic) term, Tlist.nil) Tlist.cons )
                            Tlist.cons )
                          CubeOf.Heter.hft =
                       fun s [ { tm; ty } ] ->
                        (* The type of this argument must *also* be instantiated at the correct dimension; we want the not-instantiated part. *)
                        let cod =
                          match D.compare_zero (dom_tface s) with
                          | Zero -> `Val ty
                          | Pos m -> (
                              match split_inst m (view_term ty) with
                              | Some (head_apps, _) ->
                                  (* I don't think we need to check that the instantiation arguments are correct or do anything with them; since this was obtained from typechecking the given cod, they *must* be correct. *)
                                  `Neu head_apps
                              | None ->
                                  (* Is this ever possible, or is it a bug? *)
                                  fatal (Invalid_higher_function "invalid codomain weirdness"))
                        in
                        (* The value of this argument must be read back and abstracted over the appropriate variables, namely the modal filtering of its face of the cube of variables. *)
                        let s = sface_of_tface s in
                        let (Filter_sface (fb, sfilter)) = Modality.filter_sface nfilter s in
                        let codxs = sub_variables fb xsv in
                        let (Any_ctx codctx) =
                          Ctx.variables_vis ctx
                            (Modality.filter_idempotent sfilter)
                            codxs (CubeOf.subcube fb binds) in
                        let body = readback_at codctx tm ty in
                        [ cod; Term.Lam (codxs, dom_sface s, sfilter, body) ] in
                      TubeOf.pmap { map } [ tyargs ] (Cons (Cons Nil)) in
                    (* We build the cube of codomains by reading back the lower-dimensional ones in a context extended by the appropriate partial cube of variables, and adding the top-dimensional one. *)
                    let cods =
                      let build : type m. (m, n) sface -> (m, dom * modality * mode * b) CodFam.t =
                       fun s ->
                        match pface_of_sface s with
                        | `Proper t -> (
                            let (Filter_sface (fb, sfilter)) = Modality.filter_sface nfilter s in
                            let (Any_ctx codctx) =
                              Ctx.variables_vis ctx
                                (Modality.filter_idempotent sfilter)
                                (sub_variables fb xsv) (CubeOf.subcube fb binds) in
                            match TubeOf.find ecods t with
                            | `Neu (Head_apps (head, Any args)) ->
                                Cod (sfilter, readback_neu codctx head args)
                            | `Val ty -> Cod (sfilter, readback_val codctx ty))
                        | `Id Eq -> Cod (nfilter, cod) in
                      CodCube.build n { build } in
                    ( realize status
                        (Inst
                           ( Pi
                               {
                                 x = xsv;
                                 filter = nfilter;
                                 doms = Modal (modality, plus, cdoms);
                                 cods;
                               },
                             piargs )),
                      universe mode D.zero ))))
    | App _, _ ->
        (* If there's at least one application, we slurp up all the applications and then iterate through them. *)
        let fn, args = spine { value = Synth tm.value; loc = tm.loc } in
        let stm, sty = synth_or_check_apps ctx fn args None in
        (realize status stm, sty)
    | Act (str, fa, Some { value = Synth x; loc }), _ ->
        let x = { value = x; loc } in
        if not (Modal.Mode.allows_deg (Ctx.mode ctx) fa) then
          fatal (Nonparametric_mode_degeneracy (str.value, Ctx.mode ctx));
        let ctx = Ctx.maybe_lock ctx fa in
        (* We pass on the "nosynth" error, so that we can look through multiple degeneracies before noticing a nonsynthesizing term. *)
        let sx, ety = synth ?nosynth (Kinetic `Nolet) ctx x in
        let ex = eval_term (Ctx.env ctx) sx in
        let sty =
          with_loc x.loc @@ fun () ->
          act_ty ex ety fa (Modalcell.id2 (Ctx.mode ctx)) ~err:(low_dim_arg_err str.value) in
        ( realize status (Term.Act (sx, fa, (sort_of_ty ctx (view_type sty "synth act"), `Other))),
          sty )
    | Act _, _ -> fatal_or nosynth (Nonsynthesizing "argument of degeneracy")
    | Asc (tm, ty), _ ->
        let cty =
          Reporter.try_with ~fatal:(fun d1 ->
              (* If the ascribed type doesn't typecheck, *and* if the term itself happens to already be synthesizing, we can proceed to try to synthesize it, accumulating errors from multiple sources.  This will rarely happen in normal use, since there is no need to ascribe a term that's already synthesizing, but with some alternative frontends it may. *)
              match tm.value with
              | Synth stm ->
                  Reporter.try_with ~fatal:(fun d2 ->
                      fatal (Accumulated ("ascribing synth", Snoc (Snoc (Emp, d1), d2))))
                  @@ fun () ->
                  let _ = synth status ctx (locate_opt tm.loc stm) in
                  fatal_diagnostic d1
              | _ -> fatal_diagnostic d1)
          @@ fun () -> check (Kinetic `Nolet) ctx ty (universe mode D.zero) in
        let ety = eval_term (Ctx.env ctx) cty in
        let ctm = check status ctx tm ety in
        (ctm, ety)
    | AscLam ({ value = x; loc = _ }, modality, dom, body), _ -> (
        match Modality.of_name_tgt mode modality.value with
        | Error e -> modality_fatal "synthesizing ascribed lambda" (e :> modality_error)
        | Ok (Wrap (type dom modality) (modality : (dom, modality, mode) Modality.t)) ->
            let (Locked (plus, lctx)) = Ctx.lock ctx modality in
            let cdom = check (Kinetic `Nolet) lctx dom (universe (Modality.src modality) D.zero) in
            let edom = eval_term (Ctx.env lctx) cdom in
            let newctx = Ctx.ext ctx modality x edom in
            (* We get the normal corresponding to the new variable.  The modality must be the one we added it with, and the lock must be trivial since we just added it. *)
            let xnf : dom normal =
              let (Lookup { value; modality = xmod; plus = Plus_with_locks (_, xlocks); _ }) =
                Ctx.lookup newctx (Top, None) in
              match (Modality.compare xmod modality, Modality.compare_id (Locks.cod xlocks)) with
              | Eq, Eq -> value
              | _ -> fatal (Anomaly "invalid modalities when checking AscLam") in
            let xs = singleton_variables D.zero (View.hinted x edom) in
            let filter = Modality.filter_zero modality in
            let newstatus : (mode, (b, (modality, D.zero) dim_entry) snoc, s) status =
              match status with
              | Kinetic l -> Kinetic l
              | Potential (c, args, hyp) ->
                  let arg = CubeOf.singleton xnf in
                  Potential
                    ( c,
                      Arg (args, filter, arg, ins_zero D.zero),
                      fun tm -> hyp (Lam (xs, D.zero, Modality.filter_zero modality, tm)) ) in
            let cbody, scod = synth newstatus newctx body in
            let ty =
              eval_term (Ctx.env ctx)
                (pi
                   (singleton_variables D.zero (View.hinted x edom))
                   (Modal (modality, plus, cdom))
                   (readback_val newctx scod)) in
            (Lam (xs, D.zero, filter, cbody), ty))
    | Let (x, modality, v, body), _ ->
        let ctm, Not_none ety = synth_or_check_let ?nosynth status ctx x modality v body None in
        (* The synthesized type of the body is also correct for the whole let-expression, because it was synthesized in a context where the variable is bound not just to its type but to its value, so it doesn't include any extra level variables (i.e. it can be silently "strengthened"). *)
        (ctm, ety)
    | Letrec (vtys, vs, body), _ ->
        let ctm, Not_none ety = synth_or_check_letrec ?nosynth status ctx vtys vs body None in
        (* The synthesized type of the body is also correct for the whole let-expression, because it was synthesized in a context where the variable is bound not just to its type but to its value, so it doesn't include any extra level variables (i.e. it can be silently "strengthened"). *)
        (ctm, ety)
    | Match _, Kinetic l -> (
        match l with
        | `Let -> raise Case_tree_construct_in_let
        | `Nolet ->
            emit (Bare_case_tree_construct "match");
            (* A match in a kinetic synthesizing position, we can treat like a let-binding that returns the bound (metavariable) value.  Of course we can shortcut the binding by just inserting the metavariable as the result.  This code is copied and modified from synth_or_check_let.  Note that in this case there is no evident way to give the metavariable a type before defining it, which means that with_meta_definition won't be able to set it to anything; but this shouldn't be a problem since there is also no name for this metavariable and hence no way for the user to refer to it in the body, so it doesn't need to have a type or a value. *)
            let meta =
              Meta.make_def "match" None (Ctx.mode ctx) (Ctx.raw_length ctx) (Ctx.tctx ctx)
                Potential in
            let tmstatus = Potential (Meta (meta, Ctx.env ctx), Emp, fun x -> x) in
            let sv, svty = synth tmstatus ctx tm in
            let vty = readback_val ctx svty in
            let termctx = readback_ctx ctx in
            Global.add_meta meta ~termctx ~tm:(`Defined sv) ~ty:vty ~energy:Potential;
            (Term.Meta (meta, Kinetic), svty))
    | Match { tm; window; sort = `Explicit motive; branches; refutables = _; highers }, Potential _
      -> synth_dep_match status ctx tm window branches highers motive
    | Match { tm; window; sort = `Implicit; branches; refutables = _; highers }, Potential _ ->
        emit (Matching_wont_refine ("match in synthesizing position", None));
        synth_nondep_match status ctx tm window branches highers None
    | Match { tm; window; sort = `Nondep i; branches; refutables = _; highers }, Potential _ ->
        synth_nondep_match status ctx tm window branches highers (Some i)
    | Fail e, _ -> fatal e
    (* If we're using the synthesized type of an argument as an implicit first argument: *)
    | ImplicitSApp (fn, apploc, arg), _ -> (
        (* We synthesize both function and argument *)
        let sfn, sfnty = synth (Kinetic `Nolet) ctx fn in
        let _, sargty = synth (Kinetic `Nolet) ctx arg in
        (* We read back the synthesized type, so we can put it as the first argument in the generated term. *)
        let cargty = readback_val ctx sargty in
        match view_type sfnty "ImplicitSApp" with
        | Canonical (_, Pi { x = _; filter; doms; cods }, ins, tyargs) -> (
            let Eq = eq_of_ins_zero ins in
            let modality = Modality.filter_modality filter in
            (* Only 0-dimensional non-modal applications are allowed, and the first argument must be a type. *)
            match
              ( D.compare (CubeOf.dim doms) D.zero,
                view_type (CubeOf.find_top doms) "ImplicitSApp argument",
                Modality.compare_id modality )
            with
            | Eq, Canonical (_, UU _, _, _), Eq ->
                (* We build the implicit application term and its type. *)
                let new_sfn =
                  locate_opt fn.loc
                    (Term.App
                       ( sfn,
                         BindCube.dim cods,
                         filter,
                         Modal (Modality.id mode, plus_no_lock mode, CubeOf.singleton cargty) ))
                in
                let new_sty = tyof_app cods tyargs filter (CubeOf.singleton sargty) in
                (* And then apply to the argument. *)
                let stm, sty =
                  synth_apps ctx new_sfn new_sty
                    { value = Synth fn.value; loc = fn.loc }
                    [
                      ( apploc,
                        locate_opt arg.loc (Some (Synth arg.value)),
                        locate_opt None `Explicit );
                    ] in
                (realize status stm, sty)
            | _, _, Neq -> fatal ?loc:fn.loc (Unimplemented "nonidentity modality in ImplicitSApp")
            | Eq, _, _ ->
                fatal ?loc:fn.loc (Anomaly "first argument of an ImplicitSMap is not of type Type")
            | Neq, _, _ ->
                fatal ?loc:fn.loc (Dimension_mismatch ("ImplicitSApp", CubeOf.dim doms, D.zero)))
        | _ ->
            fatal ?loc:fn.loc (Applying_nonfunction_nontype (PTerm (ctx, sfn), PVal (ctx, sfnty))))
    | SFirst (alts, arg), _ ->
        let sty = Option.map (fun arg -> snd (synth status ctx (locate_opt tm.loc arg))) arg in
        let vsty = Option.map (fun sty -> view_type sty "synth_first") sty in
        let rec go errs = function
          | [] ->
              if Bwd.is_empty errs then
                fatal
                  (Choice_mismatch (Option.fold ~some:(fun sty -> PVal (ctx, sty)) ~none:PUnit sty))
              else fatal (Accumulated ("SFirst", errs))
          | (test, alt, passthru) :: alts -> (
              match (vsty, test) with
              | Some (Canonical (_, Data { constrs = data_constrs; _ }, _, _)), `Data constrs ->
                  if
                    List.for_all
                      (fun constr ->
                        Bwd.exists (fun (data_constr, _) -> constr = data_constr) data_constrs)
                      constrs
                  then
                    Reporter.try_with ~fatal:(fun d ->
                        if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                    @@ fun () -> synth status ctx (locate_opt tm.loc alt)
                  else go errs alts
              | Some (Canonical (_, Codata { fields = codata_fields; _ }, _, _)), `Codata fields ->
                  if
                    List.for_all
                      (fun field ->
                        Bwd.exists
                          (fun (CodatafieldAbwd.Entry (codata_field, _)) ->
                            field = Field.to_string codata_field)
                          codata_fields)
                      fields
                  then
                    Reporter.try_with ~fatal:(fun d ->
                        if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                    @@ fun () -> synth status ctx (locate_opt tm.loc alt)
                  else go errs alts
              | _, `Any ->
                  Reporter.try_with ~fatal:(fun d ->
                      if passthru then go (Snoc (errs, d)) alts else fatal_diagnostic d)
                  @@ fun () -> synth status ctx (locate_opt tm.loc alt)
              | None, `Data _ | None, `Codata _ -> fatal (Anomaly "SFirst mismatch")
              | _ -> go errs alts) in
        go Emp alts
    | Calc (x, rest), _ ->
        let idm = Modality.id mode in
        let cx, ty = synth (Kinetic `Nolet) ctx x in
        let cty = readback_val ctx ty in
        let env = Ctx.env ctx in
        let ex = eval_term env cx in
        let nx : mode normal = { tm = ex; ty } in
        let creflx = Term.Act (cx, deg_zero Hott.dim, (`Other, `Other)) in
        let idty = act_value ty (deg_zero Hott.dim) (Modalcell.id2 mode) in
        let ididcty =
          Term.Act
            ( Term.Act (cty, deg_zero Hott.dim, (`Other, `Other)),
              deg_zero Hott.dim,
              (`Other, `Other) ) in
        let (Plus hh) = D.plus Hott.dim in
        let _, nz, xeqz =
          List.fold_left
            (fun (cy, ny, xeqy) (z, yeqz) ->
              let cz = check (Kinetic `Nolet) ctx z ty in
              let ez = eval_term env cz in
              match yeqz with
              | Some yeqz ->
                  let nz : mode normal = { tm = ez; ty } in
                  Reporter.try_with
                    (fun () ->
                      let yztube =
                        Hott.tube ny nz <|> Unimplemented "equational reasoning without -hott" in
                      let idyz = inst idty yztube in
                      let cyeqz = check (Kinetic `Nolet) ctx yeqz idyz in
                      let pqtube =
                        Hott.tube12 hh cx cx creflx cy cz cyeqz
                        <|> Unimplemented "equational reasoning without -hott" in
                      ( cz,
                        nz,
                        app
                          (Field
                             ( modal_id mode (Inst (ididcty, pqtube)),
                               Field.intern "trr" Hott.dim,
                               id_ins D.zero (D.zero_plus Hott.dim) ))
                          idm (plus_no_lock mode) xeqy ))
                      (* If that didn't work, we try reversing the equality and checking that instead. *)
                    ~fatal:(fun d ->
                      let zytube =
                        Hott.tube nz ny <|> Unimplemented "equational reasoning without -hott" in
                      let idzy = inst idty zytube in
                      let czeqy =
                        (* But if that also fails, we report only the error from the forwards direction. *)
                        Reporter.try_with ~fatal:(fun _ -> fatal_diagnostic d) @@ fun () ->
                        check (Kinetic `Nolet) ctx yeqz idzy in
                      let pqtube =
                        Hott.tube12 hh cx cx creflx cz cy czeqy
                        <|> Unimplemented "equational reasoning without -hott" in
                      ( cz,
                        nz,
                        app
                          (Field
                             ( modal_id mode (Inst (ididcty, pqtube)),
                               Field.intern "trl" Hott.dim,
                               id_ins D.zero (D.zero_plus Hott.dim) ))
                          idm (plus_no_lock mode) xeqy ))
              | None -> (
                  with_loc z.loc @@ fun () ->
                  match equal_at ctx ny.tm ez ty with
                  | Ok () -> (cy, ny, xeqy)
                  | Error _ -> fatal (Calc_error (PString "unequal term"))))
            (cx, nx, creflx) rest in
        let xztube = Hott.tube nx nz <|> Unimplemented "equational reasoning without -hott" in
        (realize status xeqz, inst idty xztube) in
  with_loc tm.loc @@ fun () ->
  Annotate.ctx status ctx (locate_opt tm.loc (Synth tm.value));
  let restm, resty = go () in
  Annotate.ty ctx resty;
  Annotate.tm ctx restm;
  (restm, resty)

(* Given something that can be applied, its type, and a list of arguments, check the arguments in appropriately-sized groups. *)
and synth_apps : type mode a b.
    (mode, a, b) Ctx.t ->
    (mode, b, kinetic) term located ->
    (mode, kinetic) value ->
    a check located ->
    (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list ->
    (mode, b, kinetic) term * (mode, kinetic) value =
 fun ctx sfn sty fn args ->
  (* To determine what to do, we inspect the (fully instantiated) *type* of the function being applied.  Failure of view_type here is really a bug, not a user error: the user can try to check something against an abstraction as if it were a type, but our synthesis functions should never synthesize (say) a lambda-abstraction as if it were a type. *)
  let asfn, aty, afn, aargs =
    match view_type sty "synthesizing application spine" with
    (* The obvious thing we can "apply" is an element of a pi-type. *)
    | Canonical (_, Pi { x = _; filter; doms; cods }, ins, tyargs) ->
        let Eq = eq_of_ins_zero ins in
        synth_app ctx filter sfn doms cods tyargs fn args
    (* We can also "apply" a higher-dimensional *type*, leading to a (further) instantiation of it.  Here the number of arguments must exactly match *some* integral instantiation. *)
    | Canonical (_, UU _, _, tyargs) -> synth_inst ctx sfn tyargs fn args
    (* Something that synthesizes a type that isn't a pi-type or a universe cannot be applied to anything, but this is a user error, not a bug. *)
    | _ ->
        fatal ?loc:sfn.loc (Applying_nonfunction_nontype (PTerm (ctx, sfn.value), PVal (ctx, sty)))
  in
  (* synth_app and synth_inst fail if there aren't enough arguments.  If they used up all the arguments, we're done; otherwise we continue with the rest of the arguments. *)
  match aargs with
  | [] -> (asfn.value, aty)
  | _ :: _ ->
      with_loc asfn.loc (fun () ->
          Annotate.ctx (Kinetic `Nolet) ctx afn;
          Annotate.ty ctx aty;
          Annotate.tm ctx asfn.value);
      synth_apps ctx asfn aty afn aargs

(* This is a common subroutine for synth_app and synth_inst that picks up a whole cube of arguments and checks their types.  Since in one case we need a cube of values and the other case a cube of normals, we let the caller choose. *)
and synth_arg_cube : type dom modality mode a b n c.
    not_enough:Reporter.Code.t ->
    which:string ->
    (mode, a, b) Ctx.t ->
    (dom, modality, mode) Modality.t ->
    ((dom, kinetic) value -> dom normal -> c) ->
    (n, (dom, kinetic) value) CubeOf.t ->
    Asai.Range.t option
    * a check located
    * (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list ->
    ((n, dom, modality, mode, b, kinetic) modal_term_cube * (n, c) CubeOf.t)
    * (Asai.Range.t option
      * a check located
      * (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list) =
 fun ~not_enough ~which ctx modality choose doms (sfnloc, fn, args) ->
  (* Based on the dimension of the application and whether the first argument is implicit, decide whether we are taking a whole cube of arguments or only one argument with the boundary synthesized from it. *)
  let module TakenArgs = struct
    type t =
      | Take
      | Given :
          Asai.Range.t option * (n, 'k, 'nk) D.plus * (D.zero, 'nk, 'nk, dom normal) TubeOf.t
          -> t
  end in
  let n = CubeOf.dim doms in
  let (Locked (plus, lctx)) = Ctx.lock ctx modality in
  let taken_args : TakenArgs.t =
    match (args, D.compare_zero n, Endpoints.totally_nullary n) with
    | [], _, _ -> fatal not_enough
    (* If the first argument is implicit, or if the cube would have only one element (i.e. it is 0-dimensional or consists entirely of nullary dimensions) take a whole cube. *)
    | (_, _, { value = `Implicit; _ }) :: _, Pos _, false | _, Zero, _ | _, _, true -> Take
    (* Otherwise, the first argument must be explicit and synthesizing. *)
    | (_, { value = Some (Synth toptm); loc }, { value = `Explicit; _ }) :: _, Pos _, false -> (
        (* We synthesize its type, extract the instantiation arguments, and store them to fill in the boundary arguments. *)
        let _, argty = synth (Kinetic `Nolet) lctx (locate_opt loc toptm) in
        let (Full_tube argtyargs) = get_tyargs argty "primary argument" in
        (* A function of one dimension can be applied to a primary argument of a *higher* dimension, since a cube is also a square.  So we require only that the dimension of argtyargs factors through the application dimension. *)
        match D.factor (TubeOf.inst argtyargs) (CubeOf.dim doms) with
        | Some (Factor nk) -> Given (loc, nk, argtyargs)
        | None ->
            fatal ~severity:Asai.Diagnostic.Error ?loc
              (Insufficient_dimension
                 { needed = CubeOf.dim doms; got = TubeOf.inst argtyargs; which }))
    | (_, { loc; _ }, { value = `Explicit; _ }) :: _, Pos _, false ->
        fatal ?loc (Nonsynthesizing ("primary argument with implicit " ^ which ^ " boundaries"))
  in
  let module M = Monad.State (struct
    type t =
      Asai.Range.t option
      * a check located
      * (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list
  end) in
  (* Pick up the right number of arguments for the dimension, leaving the others for a later call to synth_app.  Then check each argument against the corresponding type in "doms", instantiated at the appropriate evaluated previous arguments, and evaluate it, producing Cubes of checked terms and values.  Since each argument has to be checked against a type instantiated at the *values* of the previous ones, we also store those in a hashtable as we go. *)
  let eargtbl = Hashtbl.create 10 in
  let [ cargs; eargs ], (newloc, newfn, rest) =
    let open CubeOf.Monadic (M) in
    let open CubeOf.Infix in
    let first = ref true in
    pmapM
      {
        map =
          (fun fa [ dom ] ->
            let open Monad.Ops (M) in
            let* loc, f, ts = M.get in
            (* The type of this argument is obtained by instantiating the domain higher-dimensional type at the previous arguments. *)
            let ty =
              inst dom
                (TubeOf.build D.zero
                   (D.zero_plus (dom_sface fa))
                   {
                     build =
                       (fun fc ->
                         Hashtbl.find eargtbl (SFace_of (comp_sface fa (sface_of_tface fc))));
                   }) in
            let* ctm, tm =
              match (pface_of_sface fa, taken_args) with
              (* If we are synthesizing the implicit boundary and this is a proper face, we look up the corresponding normal value, check that it has the correct type, and read it back to get the required checked term. *)
              | `Proper pfa, Given (toploc, nk, argtyargs) ->
                  let (Plus ml) = D.plus (D.plus_right nk) in
                  let { tm = etm; ty = ety } = TubeOf.find argtyargs (pface_plus pfa nk ml) in
                  with_loc toploc (fun () ->
                      match equal_val lctx ety ty with
                      | Ok () -> ()
                      | Error why ->
                          fatal
                            (Unequal_synthesized_boundary
                               {
                                 face = fa;
                                 got = PVal (lctx, ety);
                                 expected = PVal (lctx, ty);
                                 why;
                               }));
                  let ctm = readback_at lctx etm ety in
                  return (ctm, etm)
              (* Otherwise, we pull an argument of the appropriate implicitness, check it against the correct type. *)
              | _ ->
                  let* tm =
                    match ts with
                    | [] -> with_loc loc @@ fun () -> fatal not_enough
                    | (l, t, ({ value = i; loc } as impl)) :: ts ->
                        (match (is_id_sface fa, i) with
                        | Some _, `Implicit ->
                            fatal ?loc
                              (Unexpected_implicitness
                                 ( `Implicit,
                                   "argument",
                                   "expecting explicit primary " ^ which ^ " argument" ))
                        | None, `Explicit ->
                            fatal ?loc
                              (Unexpected_implicitness
                                 ( `Explicit,
                                   "argument",
                                   "expecting implicit boundary " ^ which ^ " argument" ))
                        | _ -> ());
                        let* () = M.put (l, locate_opt l (Synth (App (f, t, impl))), ts) in
                        return t in
                  let tm =
                    match tm.value with
                    | Some value -> { value; loc = tm.loc }
                    | None -> fatal ?loc:tm.loc Invalid_nullary_application in
                  let ctm = check (Kinetic `Nolet) lctx tm ty in
                  let etm = eval_term (Ctx.env lctx) ctm in
                  return (ctm, etm) in
            (* In both cases, we store the resulting value term as a normal in the hashtable of previous values, to use in instantiating later types. *)
            let ntm = { tm; ty } in
            Hashtbl.add eargtbl (SFace_of fa) ntm;
            first := false;
            return (ctm @: [ choose tm ntm ]));
      }
      [ doms ] (Cons (Cons Nil)) (sfnloc, fn, args) in
  ((Modal (modality, plus, cargs), eargs), (newloc, newfn, rest))

and synth_app : type dom modality mode a b k n.
    (mode, a, b) Ctx.t ->
    (dom, modality, mode, k, n) Modality.filter_dim ->
    (mode, b, kinetic) term located ->
    (k, (dom, kinetic) value) CubeOf.t ->
    (n, mode * modality * dom) BindCube.t ->
    (D.zero, n, n, mode normal) TubeOf.t ->
    a check located ->
    (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list ->
    (mode, b, kinetic) term located
    * (mode, kinetic) value
    * a check located
    * (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list =
 fun ctx filter sfn doms cods tyargs fn args ->
  let (cargs, eargs), (newloc, newfn, rest) =
    synth_arg_cube ~not_enough:Not_enough_arguments_to_function
      ~which:"higher-dimensional application" ctx (Modality.filter_modality filter)
      (fun tm _ -> tm)
      doms (sfn.loc, fn, args) in
  (* Evaluate cod at these evaluated arguments and instantiate it at the appropriate values of tyargs. *)
  let output = tyof_app cods tyargs filter eargs in
  ( { value = Term.App (sfn.value, BindCube.dim cods, filter, cargs); loc = newloc },
    output,
    newfn,
    rest )

(* Pick up enough arguments to form a tube for instantiating a higher-dimensional type by a single direction, and return the result along with the remaining arguments not yet picked up.  *)
and synth_inst : type mode a b n.
    (mode, a, b) Ctx.t ->
    (mode, b, kinetic) term located ->
    (D.zero, n, n, mode normal) TubeOf.t ->
    a check located ->
    (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list ->
    (mode, b, kinetic) term located
    * (mode, kinetic) value
    * a check located
    * (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list =
 fun ctx sfn tyargs fn args ->
  let n = TubeOf.inst tyargs in
  match D.compare_zero n with
  | Zero -> fatal (Instantiating_zero_dimensional_type (PTerm (ctx, sfn.value)))
  | Pos pn ->
      (* We take enough arguments to instatiate a type of dimension n by one. *)
      let (Is_suc (type nminusone one) ((m, msuc, k) : nminusone D.t * _ * one is_singleton)) =
        suc_pos pn in
      let tyargs1 =
        TubeOf.mmap
          { map = (fun _ [ { tm; ty = _ } ] -> tm) }
          [ TubeOf.pboundary (D.zero_plus m) msuc tyargs ] in
      let (Wrap l) = Endpoints.wrapped () in
      let doms = TubeOf.to_cube_bwv k l tyargs1 in
      let module M = Monad.State (struct
        type t =
          Asai.Range.t option
          * a check located
          * (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list
      end) in
      let open Bwv.Monadic (M) in
      let idm = Modality.id (Ctx.mode ctx) in
      let (cargs, nargs), (newloc, newfn, rest) =
        match Bwv.length doms with
        | Nat (Suc _) ->
            mapM1_2
              (fun doms state ->
                let (Modal (Path (Zero, _), Plus_lock (Zero _, Zero), cargs), eargs), state =
                  synth_arg_cube ~not_enough:Not_enough_arguments_to_instantiation
                    ~which:"instantiation" ctx idm
                    (fun _ ntm -> ntm)
                    doms state in
                (((cargs : (nminusone, (mode, b, kinetic) term) CubeOf.t), eargs), state))
              doms (sfn.loc, fn, args)
        | Nat Zero -> (
            (* If instantiating a nullary dimension, we expect a single . argument. *)
            match args with
            | (l, ({ value = None; _ } as arg), i) :: rest ->
                ((Emp, Emp), (l, locate_opt l (Synth (App (fn, arg, i))), rest))
            | (_, { value = Some _; loc }, _) :: _ -> fatal ?loc Expected_nullary_application
            | [] -> fatal Not_enough_arguments_to_instantiation) in
      (* The synthesized type *of* the instantiation is itself a full instantiation of a universe, at the instantiations of the type arguments at the evaluated term arguments.  This is computed by tyof_inst. *)
      let cargs = TubeOf.of_cube_bwv m k msuc l cargs in
      let nargs = TubeOf.of_cube_bwv m k msuc l nargs in
      ( { value = Term.Inst (sfn.value, cargs); loc = newloc },
        tyof_inst (Ctx.mode ctx) tyargs nargs,
        newfn,
        rest )

(* If the head of an application spine doesn't fully synthesize, i.e. it is a possibly-degenerated abstraction, we inspect the arguments and ascriptions in the abstraction to see if we can get types for all the arguments.  Then we can try to synthesize the body of the abstraction, or check it if we are checking the whole application against a (non-dependent) output type. *)
and synth_or_check_apps : type mode a b.
    (mode, a, b) Ctx.t ->
    a check located ->
    (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list ->
    (mode, kinetic) value option ->
    (mode, b, kinetic) term * (mode, kinetic) value =
 fun ctx fn args ty ->
  match (fn.value, actions (Some fn)) with
  (* If we can fully synthesize a type for the function (that is, if it's a synthesizing term perhaps degenerated), we do that and then pass off to synth_apps to iterate through all the arguments. *)
  | Synth sfn, (_, Some { value = Synth _; _ }) ->
      let sfn, sty = synth (Kinetic `Nolet) ctx { value = sfn; loc = fn.loc } in
      let stm, sty = synth_apps ctx { value = sfn; loc = fn.loc } sty fn args in
      (stm, sty)
  (* Otherwise, we try getting information from the arguments. *)
  | _, (_, None) -> fatal (Nonsynthesizing "degeneracy of placeholder function")
  | _, (Any_deg s, Some fn) -> (
      match D.compare_zero (cod_deg s) with
      | Zero ->
          if not (Modal.Mode.allows_deg (Ctx.mode ctx) s) then
            fatal (Nonparametric_mode_degeneracy (string_of_deg s, Ctx.mode ctx));
          let ctx = Ctx.maybe_lock ctx s in
          let cfn, sty = synth_lam (dom_deg s) ctx fn ctx args ty in
          let efn = eval_term (Ctx.env ctx) cfn in
          (* Finally, we still need to degenerate that function and apply it to all the arguments. *)
          synth_apps ctx
            (locate_opt fn.loc (Term.Act (cfn, s, (`Function, `Other))))
            (act_ty efn sty s (Modalcell.id2 (Ctx.mode ctx)))
            fn args
      | Pos _ -> fatal (Unimplemented "typechecking degenerated higher-dimensional redices"))

(* A helper function for synth_or_check_apps.  It uses information from ascribed abstractions, synthesizing arguments, and supplied type to synthesize a type for the head abstraction.  It *only* uses the arguments for this purpose, and ignores them if unneeded.  Thus its return value must afterwards still be applied to the arguments.  (In particular, therefore, some of the arguments may end up being synthesized twice, which is not great.) *)
and synth_lam : type mode a b c d n.
    n D.t ->
    (mode, c, d) Ctx.t ->
    c check located ->
    (mode, a, b) Ctx.t ->
    (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located) list ->
    (mode, kinetic) value option ->
    (mode, d, kinetic) term * (mode, kinetic) value =
 fun n ctx fn argctx args ty ->
  let mode = Ctx.mode ctx in
  match (fn.value, args) with
  (* If the current function synthesizes, we do that right away and return it, ignoring the rest of the arguments. *)
  | Synth sfn, _ -> synth (Kinetic `Nolet) ctx { value = sfn; loc = fn.loc }
  (* Otherwise, if we're out of arguments, we assume we have a non-dependent function type and check the body against the overall type that must have been supplied to check against. *)
  | _, [] -> (
      match ty with
      | Some ty ->
          (* We un-act on the checking type to obtain a type for the function inside the degeneracy *)
          let uty =
            unact_ty ~err:(Unimplemented "typechecking degenerated redexes with arity 0") ty n in
          let cfn = check (Kinetic `Nolet) ctx fn uty in
          (cfn, uty)
      | None ->
          fatal ?loc:fn.loc (Nonsynthesizing "head of application spine in synthesizing position"))
  (* If there are arguments left, and the head is an abstraction with a type ascribed to its variable, we use that type. *)
  | ( Lam
        {
          name;
          cube = { value = `Normal; _ };
          implicit = `Explicit;
          dom = Some (modality, dom);
          body;
        },
      _ :: _ ) -> (
      match Modality.of_name_tgt mode modality.value with
      | Error e -> modality_fatal "synthesizing ascribed lambda" (e :> modality_error)
      | Ok (Wrap (type dom modality) (modality : (dom, modality, mode) Modality.t)) ->
          let (Locked (plus, lctx)) = Ctx.lock ctx modality in
          (* As in synthesizing an AscLam, we check the supplied domain and extend the context. *)
          let cdom = check (Kinetic `Nolet) lctx dom (universe (Modality.src modality) D.zero) in
          let edom = eval_term (Ctx.env lctx) cdom in
          let newctx = Ctx.ext ctx modality name.value edom in
          let xs = singleton_variables D.zero (View.hinted name.value edom) in
          (* Pull off either one explicit argument or a cube of mostly-implicit ones, of the correct dimension. *)
          let module M = CubeOf.Monadic (Monad.State (struct
            type t =
              (Asai.Range.t option * a check option located * [ `Implicit | `Explicit ] located)
              list
          end))
          in
          let _, rest =
            M.buildM n
              {
                build =
                  (fun _ -> function
                    | [] -> fatal Not_enough_arguments_to_function
                    | _ :: xs -> ((), xs));
              }
              args in
          (* Then we proceed recursively to check the body of the abstraction. *)
          let cbody, scod = synth_lam n newctx body argctx rest ty in
          let scod =
            eval_term (Ctx.env ctx)
              (pi
                 (singleton_variables D.zero (View.hinted name.value edom))
                 (Modal (modality, plus, cdom))
                 (readback_val newctx scod)) in
          (Lam (xs, D.zero, Modality.filter_zero modality, cbody), scod))
  (* If there are arguments left, and the head is a normal explicit abstraction (no higher abstractions are allowed), and the application is also explicit (but might be higher-dimensional, if there is a degeneracy), we try synthesizing a type from the argument. *)
  | ( Lam { name; cube = { value = `Normal; _ }; implicit = `Explicit; dom = None; body },
      (_, arg, { value = `Explicit; _ }) :: args ) -> (
      match arg.value with
      | Some (Synth sarg) ->
          let _, sargty = synth (Kinetic `Nolet) argctx (locate_opt arg.loc sarg) in
          let edom =
            unact_ty ~err:(Unimplemented "typechecking degenerated redexes with arity 0") sargty n
          in
          (* In this case there cannot be a nonidentity modality, since there is nowhere for the user to specify the modality. *)
          let idm = Modality.id (Ctx.mode ctx) in
          (* Finally we can extend the context by this obtained domain. *)
          let newctx = Ctx.ext ctx idm name.value edom in
          let xs = singleton_variables D.zero (View.hinted name.value edom) in
          (* Then we proceed again recursively to check the body of the abstraction. *)
          let cbody, scod = synth_lam n newctx body argctx args ty in
          let cdom = readback_val ctx edom in
          let scod =
            eval_term (Ctx.env ctx)
              (pi
                 (singleton_variables D.zero (View.hinted name.value edom))
                 (Modal (idm, plus_no_lock mode, cdom))
                 (readback_val newctx scod)) in
          (Lam (xs, D.zero, Modality.filter_zero idm, cbody), scod)
      | None -> fatal ?loc:arg.loc Invalid_nullary_application
      | _ ->
          let extra_remarks = [ Asai.Diagnostic.loctext ?loc:arg.loc "argument" ] in
          fatal ?loc:fn.loc ~extra_remarks
            (Nonsynthesizing "head of application spine and corresponding argument"))
  | _ ->
      fatal ?loc:fn.loc (Nonsynthesizing "head of higher-dimensional or implicit application spine")

(* Check a list of terms against the types specified in a telescope, evaluating the latter in a supplied environment and in the context of the previously checked terms, and instantiating them at values given in a tube.  See description in context of the call to it above during typechecking of a constructor. *)
and check_at_tel : type mode n a b c bc e.
    Constr.t ->
    (mode, a, e) Ctx.t ->
    (mode, n, b) env ->
    (* This list of terms to check must have the same length *)
    a check located list ->
    (* as this telescope (namely, the Fwn 'c') *)
    (mode, b, c, bc) Telescope.t ->
    (* and as this vector of tubes. *)
    ((D.zero, n, n, (mode, kinetic) modal_value) TubeOf.t, c) Vec.t ->
    (mode, n, bc) env * (n, mode, e, kinetic) any_modal_term_cube list =
 fun c ctx env tms tys tyargs ->
  match (tms, tys, tyargs) with
  | [], Emp, [] -> (env, [])
  | ( tm :: tms,
      Ext
        (type modality)
        (( _,
           Modal
             (type dom am)
             ((modality, bplus, ty) : _ * (_, mode, modality, dom, am) plus_lock * _),
           tys ) :
          _ * (mode, modality, b, kinetic) modal_term * _),
      tyargs :: tyargs_rest ) ->
      (* The argument to check is k-dimensional, where k is the modal filtering of the dimension n of the entire constructor. *)
      let n = dim_env env in
      let (Has_filter filter) = Modality.filter modality n in
      let k = Modality.filtered n filter in
      let filter_face = Modality.sface_of_filter n filter in
      (* We lock the context and environment, and act on the environment by the filter face before evaluating the type. *)
      let (Locked (eplus, lctx)) = Ctx.lock ctx modality in
      let lenv = key_env env (Modalcell.id modality) bplus in
      let alenv = act_env lenv (opt_op_of_opt_sface filter_face) in
      let ety = eval_term alenv ty in
      (* Now we build the boundary tube for this type. *)
      let tyargtbl = Hashtbl.create 10 in
      let tyarg =
        TubeOf.build D.zero (D.zero_plus k)
          {
            build =
              (fun fa ->
                (* The value associated to some face of k in the cube of arguments is derived from the corresponding argument of the n-dimensional constructor associated to the corresponding face of n lifted along the filter, as in equality-testing and readback. *)
                let (Pface_filter (_, fb)) = Modality.pface_filter n fa filter in
                let (Modal (argmod, argtm)) = TubeOf.find tyargs fb in
                match Modality.compare argmod modality with
                | Neq -> fatal (Modality_mismatch (`Internal, "check_at_tel", argmod, modality))
                | Eq ->
                    let fa = sface_of_tface fa in
                    let fb = sface_of_tface fb in
                    let argty : (dom, kinetic) value =
                      inst
                        (eval_term
                           (act_env lenv
                              (opt_op_of_opt_sface (comp_opt_sface filter_face (opt_of_sface fa))))
                           ty)
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_sface fb))
                           {
                             build =
                               (fun fc ->
                                 Hashtbl.find tyargtbl
                                   (SFace_of (comp_sface fb (sface_of_tface fc))));
                           }) in
                    let argnorm : dom normal = { tm = argtm; ty = argty } in
                    Hashtbl.add tyargtbl (SFace_of fb) argnorm;
                    argnorm);
          } in
      let ity = inst ety tyarg in
      let ctm = check (Kinetic `Nolet) lctx tm ity in
      let ctms = TubeOf.mmap { map = (fun _ [ t ] -> readback_nf lctx t) } [ tyarg ] in
      let etm = eval_term (Ctx.env lctx) ctm in
      let newenv, newargs =
        check_at_tel c ctx
          (Ext
             {
               env;
               plus = D.plus_zero (TubeOf.inst tyarg);
               filter;
               filtered = Modality.filter_zero modality;
               values = `Ok (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton etm));
             })
          tms tys tyargs_rest in
      (newenv, Modal (filter, eplus, TubeOf.plus_cube ctms (CubeOf.singleton ctm)) :: newargs)
  | _ ->
      fatal
        (Wrong_number_of_arguments_to_constructor
           (c, List.length tms - Fwn.to_int (Telescope.length tys)))

(* Given a context and a raw telescope, we can check it to produce a checked telescope, a new context extended by that telescope, and a function for extending other contexts by that telescope.  The returned boolean indicates whether this could be the telescope of arguments of a constructor of a *discrete* datatype.  This requires knowing the collection of currently-being-defined mutual constants, since discrete types can appear recursively in the arguments of their constructors. *)
and check_tel : type mode a b c ac.
    ?discrete:unit Constant.Map.t ->
    (mode, a, b) Ctx.t ->
    (a, c, ac) Raw.tel ->
    (mode, a, b, c, ac) checked_tel * bool =
 fun ?discrete ctx tel ->
  match tel with
  | Emp -> (Checked_tel (Emp, ctx), Option.is_some discrete)
  | Ext (x, modality, ty, tys) -> (
      match Modality.of_name_tgt (Ctx.mode ctx) modality.value with
      | Error e -> modality_fatal "checking a telescope" (e :> modality_error)
      | Ok (Wrap modality) ->
          if not (Modality.tangible modality) then fatal (Intangible_modality modality);
          let (Locked (plus, lctx)) = Ctx.lock ctx modality in
          let cty = check (Kinetic `Nolet) lctx ty (universe (Modality.src modality) D.zero) in
          let ety = eval_term (Ctx.env lctx) cty in
          let _, newnfs = dom_vars ctx modality (CubeOf.singleton ety) in
          let ctx = Ctx.cube_vis ctx (Modality.filter_zero modality) x newnfs in
          let Checked_tel (ctys, ctx), disc = check_tel ?discrete ctx tys in
          let tydisc = is_discrete ?discrete ety in
          (Checked_tel (Ext (x, Modal (modality, plus, cty), ctys), ctx), disc && tydisc))

(* We also need to be able to synthesize a mode for a definition.  In theory we could incorporate this into 'synth' to avoid multiple traversals, but the attempt proved very complicated, and not much of the term should need to be traversed to find its mode.  You might think we should do this in a "context" of raw variables with possibly-known modes so we can look up the modes of variables, but in practice that's not useful: whenever a variable is introduced, if we *know* its mode, then we can immediately deduce the mode of the whole term anyway. *)
let rec synth_mode : type a. a check located -> Modal.Mode.wrapped option =
 fun tm ->
  (* If there is a unique mode in the current theory, we can just return that. *)
  match Modal.Mode.unique () with
  | Some mode -> Some mode
  | None -> (
      match tm.value with
      (* The body of a lambda always has the same mode as the lambda itself, if we can tell that.  If that fails, then if the variable is ascribed we can use that. *)
      | Lam { body; dom; _ } -> (
          match synth_mode body with
          | Some mode -> Some mode
          | None -> (
              match dom with
              | Some (modality, dom) -> (
                  match synth_mode dom with
                  | Some (Wrap dmode) -> (
                      match Modality.of_name_src modality.value dmode with
                      | Ok (Wrap modality) -> Some (Wrap (Modality.tgt modality))
                      | Error _ -> None)
                  | None -> None)
              | None -> None))
      (* We can't tell the mode of a struct from its terms, since they could be modally annotated, and the information about those annotations is contained in the record type it checks against. *)
      | Struct (_, _) -> None
      (* We can't tell the mode of a constructor from those of its arguments, since it might have modal arguments, and that information is contained in the datatype it checks against. *)
      | Constr (_, _) | Numeral _ | Empty_co_match -> None
      (* In principle, we could synthesize the mode of a datatype as soon as it has some constructor with an argument, perhaps modally annotated.  However, this seems unlikely to be very useful, so we punt for now, and similarly for other canonical types.  *)
      | Data _ | Codata _ | Record _ | SelfRecord _ -> None
      | Refute (_, _) -> None
      | Hole _ -> None
      | Realize _ -> None
      | ImplicitApp (_, _) -> None
      | Embed _ -> .
      | First _ -> None
      | Oracle _ -> None
      | Weaken (x, Eq) -> synth_mode (locate_opt tm.loc x)
      | Synth (Var (_, _)) -> None
      (* Each constant stores its mode. *)
      | Synth (Const name) ->
          let (Definition { mode; _ }) = Global.find name in
          Some (Wrap mode)
      (* A field projection's mode is the mode of the term being projected, unless there is a modal locking annotation, in which case it is the target of that modality (the annotation names the left adjoint, whose source is the term's mode and whose target is the projection's mode). *)
      | Synth (Field (x, _, None)) -> synth_mode (locate_opt tm.loc (Synth x.value))
      | Synth (Field (x, _, Some lock)) -> (
          match synth_mode (locate_opt tm.loc (Synth x.value)) with
          | Some (Wrap xmode) -> (
              match Modality.of_name_src lock.value xmode with
              | Ok (Wrap modality) -> Some (Wrap (Modality.tgt modality))
              | Error _ -> None)
          | None -> None)
      | Synth (Pi (_, modality, dom, cod)) -> (
          match synth_mode cod with
          | Some mode -> Some mode
          | None -> (
              match synth_mode dom with
              | Some (Wrap dmode) -> (
                  match Modality.of_name_src modality.value dmode with
                  | Ok (Wrap modality) -> Some (Wrap (Modality.tgt modality))
                  | Error _ -> None)
              | None -> None))
      | Synth (HigherPi (_, modality, dom, cod)) -> (
          match synth_mode (locate_opt cod.loc (Synth cod.value)) with
          | Some mode -> Some mode
          | None -> (
              match synth_mode (locate_opt dom.loc (Synth dom.value)) with
              | Some (Wrap dmode) -> (
                  match Modality.of_name_src modality.value dmode with
                  | Ok (Wrap modality) -> Some (Wrap (Modality.tgt modality))
                  | Error _ -> None)
              | None -> None))
      | Synth (InstHigherPi (_, _doms, cod)) ->
          (* MODALTODO: Try inspecting the domains too, if the codomain fails *)
          synth_mode cod
      (* The mode of an application is always the mode of the function *)
      | Synth (App (fn, _, _)) -> synth_mode fn
      | Synth (Asc (tm, ty)) -> (
          match synth_mode ty with
          | Some mode -> Some mode
          | None -> synth_mode tm)
      | Synth (AscLam (_, modality, dom, body)) -> (
          match synth_mode (locate_opt body.loc (Synth body.value)) with
          | Some mode -> Some mode
          | None -> (
              match synth_mode dom with
              | Some (Wrap dmode) -> (
                  match Modality.of_name_src modality.value dmode with
                  | Ok (Wrap modality) -> Some (Wrap (Modality.tgt modality))
                  | Error _ -> None)
              | None -> None))
      | Synth (UU mode) -> Some (Wrap mode)
      | Synth (Let (_, _, _, body)) -> synth_mode body
      | Synth (Letrec (_, _, body)) -> synth_mode body
      | Synth (Act (_, _, Some ({ value = Synth _; _ } as x))) -> synth_mode x
      | Synth (Act (_, _, Some x)) -> (
          match synth_mode x with
          | Some mode -> Some mode
          | None ->
              (* We report this error here so it's the correct one; otherwise we'd get "can't synthesize a mode" which is misleading. *)
              fatal ?loc:tm.loc (Nonsynthesizing "argument of degeneracy"))
      | Synth (Act (_, _, None)) -> None
      (* The mode of a match is the mode of any of its branches. *)
      | Synth (Match { branches; _ }) ->
          Bwd.fold_right
            (fun (_, Branch (_, _, body)) acc ->
              match acc with
              | Some mode -> Some mode
              | None -> synth_mode body)
            branches None
      | Synth (Fail _) -> None
      | Synth (ImplicitSApp (fn, _, _)) -> synth_mode (locate_opt fn.loc (Synth fn.value))
      | Synth (SFirst (_, _)) -> None
      | Synth (Calc (_, _)) -> None)

let rec synth_mode_tel : type a b ab. (a, b, ab) Raw.tel -> Modal.Mode.wrapped option = function
  | Emp -> None
  | Ext (_, modality, ty, tel) -> (
      match synth_mode ty with
      | Some (Wrap dmode) -> (
          match Modality.of_name_src modality.value dmode with
          | Ok (Wrap modality) -> Some (Wrap (Modality.tgt modality))
          | Error _ -> None)
      | None -> synth_mode_tel tel)
