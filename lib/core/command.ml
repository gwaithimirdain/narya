open Bwd
open Util
open Tbwd
open Dim
open Raw
open Term
open Value
open Norm
open Check
open Readback
open Reporter
open Asai.Range

module ModeState = struct
  type t = { interactive : bool }
end

module Mode = Algaeff.Reader.Make (ModeState)

let () = Mode.register_printer (function `Read -> Some "unhandled Command.Mode.read effect")

(* A mutual "def" command can contain multiple constant definitions, each one checking or synthesizing.  *)
type defconst =
  | Def_check : {
      params : (N.zero, 'b, 'c) Raw.tel;
      ty : 'c check located;
      tm : 'c check located;
    }
      -> defconst
  | Def_synth : { params : (N.zero, 'b, 'c) Raw.tel; tm : 'c synth located } -> defconst

type t =
  | Axiom : {
      name : Constant.t;
      params : (N.zero, 'b, 'c) Raw.tel;
      ty : 'c check located;
      parametric : bool;
    }
      -> t
  | Def : (Constant.t * defconst) list -> t
  | Solve :
      Global.data
      * ('b, 's) status
      * ('a, 'b) termctx
      * 'a check located
      * ('b, kinetic) term
      * (('b, 's) term -> unit)
      -> t

(* When checking a mutual "def", we first check all the parameter telescopes, and the types in the checking cases when they are provided.  Here are the outputs of that stage, saving the as-yet-unchecked raw term along with its checked parameters and type. *)
type defined_const =
  | Defined_check : {
      const : Constant.t;
      bplus : (N.zero, 'c, 'ac) Fwn.bplus;
      params : (emp, 'c, 'bc) Telescope.t;
      ty : ('bc, kinetic) term;
      tm : 'ac check located;
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
let check_term (def : defined_const) (discrete : unit Constant.Map.t option) :
    Constant.t * (emp, potential) term =
  match def with
  | Defined_check { const; bplus; params; ty; tm } ->
      (* It's essential that we evaluate the type at this point, rather than sooner, so that the evaluation uses the *definitions* of previous constants in the mutual block and not just their types.  For the same reason, we need to re-evaluate the telescope of parameters. *)
      let ctx = eval_append Ctx.empty bplus params in
      let ety = eval_term (Ctx.env ctx) ty in
      let tm =
        Ctx.lam ctx
          (check ?discrete
             (Potential (Constant (const, D.zero), Ctx.apps ctx, Ctx.lam ctx))
             ctx tm ety) in
      Global.set const (`Defined tm, `Maybe_parametric);
      (const, tm)
  | Defined_synth { const; params; tm } ->
      let Checked_tel (cparams, ctx), _ = check_tel Ctx.empty params in
      let ctm, ety =
        synth (Potential (Constant (const, D.zero), Ctx.apps ctx, Ctx.lam ctx)) ctx tm in
      let cty = readback_val ctx ety in
      let ty = Telescope.pis cparams cty in
      let tm = Ctx.lam ctx ctm in
      Global.add const ty (`Defined tm, `Maybe_parametric);
      (const, tm)

(* Iterate through a collection of such things checking them all, and then verify whether they are all potentially-discrete datatypes.  If so, redefine them all to be actually discrete (`Yes instead of `Maybe).  Returns a list of constant names to print, and whether they are discrete. *)
let check_terms (defs : defined_const list) (discrete : unit Constant.Map.t option) :
    printable list * bool * bool =
  let rec go defs defineds =
    match defs with
    | [] ->
        let open Mbwd.Monadic (Monad.State (struct
          type t = bool
        end)) in
        let discrete_defineds, disc =
          mmapM
            (fun [ (c, def) ] disc ->
              let discrete_def, disc_def = Discrete.discrete_def def in
              ((c, discrete_def), disc && disc_def))
            [ defineds ] true in
        let p = Global.get_parametric () in
        let parametric = (p :> [ `Parametric | `Nonparametric | `Maybe_parametric ]) in
        ( Bwd_extra.to_list_map
            (fun (c, def) ->
              Global.set c (`Defined def, parametric);
              PConstant c)
            (if disc then discrete_defineds else defineds),
          disc,
          p = `Parametric )
    | d :: defs ->
        let c, v = check_term d discrete in
        go defs (Snoc (defineds, (c, v))) in
  go defs Emp

(* When checking a "def", therefore, we first iterate through checking the parameters and types, and then go back and check all the terms.  Moreover, whenever we check a type, we temporarily define the corresponding constant as an axiom having that type, so that its type can be used recursively in typechecking its definition, as well as the types of later mutual constants and the definitions of any other mutual constants. *)
let check_defs (defs : (Constant.t * defconst) list) : printable list * bool * bool =
  let rec go defs discrete defineds =
    match defs with
    | [] -> check_terms (Bwd.to_list defineds) discrete
    | (const, Def_check { params; ty; tm }) :: defs ->
        let bplus = Raw.bplus_of_tel params in
        let Checked_tel (params, ctx), disc = check_tel ?discrete Ctx.empty params in
        let ty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
        let pi_cty = Telescope.pis params ty in
        (* We set the type now; the value will be added later.  We mark it as "maybe parametric" so that we can detect if it is used behind an external degeneracy. *)
        Global.add const pi_cty (`Axiom, `Maybe_parametric);
        go defs
          (if disc then Option.map (Constant.Map.add const ()) discrete else None)
          (Snoc (defineds, Defined_check { const; bplus; params; ty; tm }))
    | (const, Def_synth { params; tm }) :: defs ->
        Global.add_error const (Synthesizing_recursion (Reporter.PConstant const));
        go defs None (Snoc (defineds, Defined_synth { const; params; tm })) in
  go defs (if Discrete.enabled () then Some Constant.Map.empty else None) Emp

let execute : t -> unit = function
  | Axiom { name; params; ty; parametric } ->
      if parametric then Global.set_parametric name else Global.set_nonparametric None;
      let Checked_tel (params, ctx), _ = check_tel Ctx.empty params in
      let cty = check (Kinetic `Nolet) ctx ty (universe D.zero) in
      let cty = Telescope.pis params cty in
      let p = Global.get_parametric () in
      Global.add name cty (`Axiom, (p :> [ `Parametric | `Nonparametric | `Maybe_parametric ]));
      Global.end_command (fun holes ->
          Some (Constant_assumed { name = PConstant name; parametric; holes }))
  | Def defs ->
      Global.set_maybe_parametric ();
      let names, discrete, parametric = check_defs defs in
      Global.end_command (fun holes ->
          Some (Constant_defined { names; discrete; parametric; holes }))
  | Solve (global, status, termctx, tm, ty, callback) ->
      if not (Mode.read ()).interactive then fatal (Forbidden_interactive_command "solve");
      let ctm =
        Global.run_command_with ~init:global (fun h -> Some (Hole_solved h)) @@ fun () ->
        let ctx = Norm.eval_ctx termctx in
        let ety = Norm.eval_term (Ctx.env ctx) ty in
        Check.check status ctx tm ety in
      callback ctm
