open Bwd
open Util
open Modal
open Tctx
open Dim
open Raw
open Term
open Value
open Norm
open Check
open Readback
open Reporter
open Asai.Range

(* A mutual "def" command can contain multiple constant definitions, each one checking or synthesizing.  *)
type defconst =
  | Def_check : {
      params : (N.zero, 'b, 'c) Raw.tel;
      ty : 'c check located;
      (* We make the term lazy so that we can wait to process it until after the constant name is defined in the scope. *)
      tm : 'c check located Lazy.t;
    }
      -> defconst
  | Def_synth : { params : (N.zero, 'b, 'c) Raw.tel; tm : 'c synth located } -> defconst

(* The parameters and type of an axiom. *)
type axiom_type =
  | Axiom_type : { params : (N.zero, 'b, 'c) Raw.tel; ty : 'c check located } -> axiom_type

type t =
  (* We make the parameters and type of an axiom lazy so that if processing them fails, that failure happens inside the handler in [execute] below that makes the axiom an error. *)
  | Axiom : { name : Constant.t; ty : axiom_type Lazy.t; parametric : bool } -> t
  (* We make the constant lazy so we can wait to create it, and in particular put it in scope, until after the type is checked, so as to avoid "very dependent types" where the object appears in its own type.  And we make the parameters and type lazy so that we can wait to process them until after previous definitions in the mutual block are defined in the scope, and so that if processing them fails, that failure happens inside the handler in [check_defs] below that makes the constant an error. *)
  | Def : (Constant.t Lazy.t * defconst Lazy.t) list -> t

(* When checking a mutual "def", we first check all the parameter telescopes, and the types in the checking cases when they are provided.  Here are the outputs of that stage, saving the as-yet-unchecked raw term along with its checked parameters and type. *)
type defined_const =
  | Defined_check : {
      const : Constant.t;
      bplus : (N.zero, 'c, 'ac) Fwn.bplus;
      mode : 'mode Mode.t;
      params : ('mode, 'mode emp, 'c, 'bc) Telescope.t;
      ty : ('mode, 'bc, kinetic) term;
      tm : 'ac check located Lazy.t;
    }
      -> defined_const
  | Defined_synth : {
      const : Constant.t;
      (* We don't bother pre-checking the parameter telescopes of a synthesizing one, since it can't be used in other ones anyway. *)
      params : (N.zero, 'b, 'c) Raw.tel;
      tm : 'c synth located;
    }
      -> defined_const

(* Given such a thing, we can proceed to check or synthesize the term, producing the type and defined value for the constant, and then define it.  This function returns the constant name as well as the checked term.  *)
type checked_term =
  | Checked : Constant.t * 'mode Mode.t * ('mode, 'mode emp, potential) term -> checked_term

let check_term (def : defined_const) : checked_term =
  match def with
  | Defined_check { const; bplus; mode; params; ty; tm } ->
      Meta.with_owner const @@ fun () ->
      (* It's essential that we evaluate the type at this point, rather than sooner, so that the evaluation uses the *definitions* of previous constants in the mutual block and not just their types.  For the same reason, we need to re-evaluate the telescope of parameters.  If one of them failed, its variable has a failed type, but the term can still be checked. *)
      let ctx = eval_append (Ctx.empty mode) bplus params in
      let ety = eval_term (Ctx.env ctx) ty in
      let tm =
        Ctx.lam ctx
          (check
             (Potential (Constant (const, Ctx.mode ctx, D.zero), Ctx.apps ctx, Ctx.lam ctx))
             ctx (Lazy.force tm) ety) in
      Global.set const mode ~parametric:`Maybe_parametric tm;
      Checked (const, mode, tm)
  | Defined_synth { const; params; tm } ->
      Meta.with_owner const @@ fun () ->
      let (Wrap mode) =
        match synth_mode_tel params with
        | Some mode -> mode
        | None -> (
            match synth_mode (locate_opt tm.loc (Synth tm.value)) with
            | Some mode -> mode
            | None -> fatal (Non_mode_synthesizing "synthesizing def")) in
      (* If some of the parameters fail to typecheck, we go on to check the others, and then the term, in a context where the failed ones are variables of failed type.  As for a checking constant, they are then Failed in the type of the constant.  If the term fails to synthesize, it has no type, so both it and its type (after the parameters) are Failed, so that an application of the constant can still check its arguments. *)
      let (Checked_tel (cparams, ctx)) = check_tel (Ctx.empty mode) params in
      let ctm, cty =
        Reporter.mortalize ~fallback:(fun () -> (Term.Failed Potential, Term.Failed Kinetic))
        @@ fun () ->
        let ctm, ety =
          synth
            (Potential (Constant (const, Ctx.mode ctx, D.zero), Ctx.apps ctx, Ctx.lam ctx))
            ctx tm in
        (ctm, readback_val ctx ety) in
      let ty = Telescope.pis cparams cty in
      let tm = Ctx.lam ctx ctm in
      Global.add const (Definition { mode; ty; tm = `Defined tm; parametric = `Maybe_parametric });
      Checked (const, mode, tm)

(* If checking the term of a constant fails, we define it to be a failed term, so that later constants in the mutual block can still use it, at its type, but anything that needs to inspect its value fails silently.  A synthesizing constant whose term fails is already defined as failed, with a failed type, by check_term; it only reaches here if we couldn't determine its mode, in which case it becomes an error. *)
let fail_term (def : defined_const) : unit =
  match def with
  | Defined_check { const; mode; _ } ->
      Global.set const mode ~parametric:`Maybe_parametric (Failed Potential)
  | Defined_synth { const; _ } -> Global.add_error const (Dependent "failed definition")

(* Iterate through a collection of such things checking them all, and then redefine them all with their final parametricity.  If one of them fails, we report the error and go on to check the others.  Returns a list of constant names to print, and whether they are parametric. *)
let check_terms (defs : defined_const list) : printable list * bool =
  let rec go defs defineds =
    match defs with
    | [] ->
        let p = Global.get_parametric () in
        let parametric = (p :> [ `Parametric | `Nonparametric | `Maybe_parametric ]) in
        ( Bwd_extra.to_list_map
            (fun (Checked (c, mode, def)) ->
              Global.set c mode ~parametric def;
              PConstant c)
            defineds,
          p = `Parametric )
    | d :: defs ->
        let defineds =
          Reporter.mortalize ~fallback:(fun () ->
              fail_term d;
              defineds)
          @@ fun () -> Snoc (defineds, check_term d) in
        go defs defineds in
  go defs Emp

(* The checked parameters and type of an axiom or a checking constant, with 'b the number of parameters. *)
type 'b checked_type =
  | Checked_type : {
      mode : 'mode Mode.t;
      params : ('mode, 'mode emp, 'b, 'bc) Telescope.t;
      ty : ('mode, 'bc, kinetic) term;
    }
      -> 'b checked_type

(* Check the parameters and type of an axiom or a checking constant, in the mode that they synthesize.  The constant is the owner of any metavariables created. *)
let check_type_of : type b c.
    string -> Constant.t -> (N.zero, b, c) Raw.tel -> c check located -> b checked_type =
 fun which const params ty ->
  Meta.with_owner const @@ fun () ->
  let (Wrap mode) =
    match synth_mode_tel params with
    | Some mode -> mode
    | None -> (
        match synth_mode ty with
        | Some mode -> mode
        | None -> fatal (Non_mode_synthesizing which)) in
  (* If some of the parameters fail to typecheck, we go on to check the others, and the type in a context where the failed ones are variables of failed type, so as to report any other errors.  The failed parameters are then Failed in the type of the constant, so that an application of it can still check its other arguments, while checking an argument against a failed type fails silently.  Likewise, if the type fails to typecheck, it is Failed, so that an application of the constant can still check its arguments, while anything that needs to inspect its (eventual) type fails silently. *)
  let (Checked_tel (params, ctx)) = check_tel (Ctx.empty mode) params in
  let ty =
    Reporter.mortalize ~fallback:(fun () -> Term.Failed Kinetic) @@ fun () ->
    check (Kinetic `Nolet) ctx ty (universe mode D.zero) in
  Checked_type { mode; params; ty }

(* Check the parameters and type of one constant in a mutual "def", and define it as an axiom with that type. *)
let check_type (const : Constant.t Lazy.t) (defconst : defconst) : Constant.t * defined_const =
  match defconst with
  | Def_check { params; ty; tm } ->
      let const = Lazy.force const in
      let (Checked_type { mode; params = cparams; ty }) =
        check_type_of "checking def" const params ty in
      (* We set the type now; the value will be added later.  We mark it as "maybe parametric" so that we can detect if it is used behind an external degeneracy. *)
      Global.add const
        (Definition
           { mode; ty = Telescope.pis cparams ty; tm = `Axiom; parametric = `Maybe_parametric });
      ( const,
        Defined_check { const; bplus = Raw.bplus_of_tel params; mode; params = cparams; ty; tm } )
  | Def_synth { params; tm } ->
      let const = Lazy.force const in
      Global.add_error const (Synthesizing_recursion (Reporter.PConstant const));
      (const, Defined_synth { const; params; tm })

(* When checking a "def", therefore, we first iterate through checking the parameters and types, and then go back and check all the terms.  Moreover, whenever we check a type, we temporarily define the corresponding constant as an axiom having that type, so that its type can be used recursively in typechecking its definition, as well as the types of later mutual constants and the definitions of any other mutual constants.  If some of its parameters, or its type, fail to typecheck, they are recorded as Failed (see check_type_of), and its term is still checked, so as to report any errors in it that don't depend on the failed parts.  Only if checking its type fails altogether, such as if we can't determine its mode, do we make the constant an error, so that later constants that use it fail silently, and go on to check the others (but not its own term). *)
let check_defs (defs : (Constant.t Lazy.t * defconst Lazy.t) list) : printable list * bool =
  let rec go defs beingdefined defineds =
    match defs with
    | [] ->
        (* The bodies are checked knowing the set of all the constants of this mutual block, so that occurrences of them in datatype constructor types can be detected as recursive.  (This set must contain exactly the being-defined constants, since real axioms appearing in constructor types are not recursion.) *)
        Positivity.run_beingdefined beingdefined @@ fun () -> check_terms (Bwd.to_list defineds)
    | (const, defconst) :: defs -> (
        match
          Reporter.mortalize ~fallback:(fun () -> None) @@ fun () ->
          Some (check_type const (Lazy.force defconst))
        with
        | Some (const, defined) ->
            go defs (Constant.Map.add const () beingdefined) (Snoc (defineds, defined))
        | None ->
            let const = Lazy.force const in
            Global.add_error const (Dependent "failed type of definition");
            go defs (Constant.Map.add const () beingdefined) defineds) in
  go defs Constant.Map.empty Emp

let execute : t -> int option * (int -> Reporter.Code.t option) = function
  (* We let Parser.Command do the calling of Global.run_command etc. *)
  | Axiom { name; ty; parametric } ->
      if parametric then Global.set_parametric name else Global.set_nonparametric None;
      (* If some of the parameters or the type of the axiom fail to typecheck, they are recorded as Failed (see check_type_of).  If checking the axiom fails altogether, such as if we can't determine its mode, we make the constant an error, so that later commands that use it fail silently. *)
      ( Reporter.try_with ~fatal:(fun d ->
            Global.add_error name (Dependent "failed axiom");
            fatal_diagnostic d)
      @@ fun () ->
        let (Axiom_type { params; ty }) = Lazy.force ty in
        let (Checked_type { mode; params; ty }) = check_type_of "axiom" name params ty in
        let p = (Global.get_parametric () :> [ `Parametric | `Nonparametric | `Maybe_parametric ]) in
        Global.add name
          (Definition { mode; ty = Telescope.pis params ty; tm = `Axiom; parametric = p }) );
      (None, fun holes -> Some (Constant_assumed { name = PConstant name; parametric; holes }))
  | Def defs ->
      Global.set_maybe_parametric ();
      let names, parametric = check_defs defs in
      (None, fun holes -> Some (Constant_defined { names; parametric; holes }))
