open Util
open Tbwd
open Reporter
open Dim
open Term
open Value
open Domvars
open Act
open Norm
open Dimbwd
open Printable
module Binding = Ctx.Binding

(* Wrapping the "Displaying" module in another module called "Readback" and opening that module allows us to refer to the module as just "Displaying" here, but exports it as "Readback.Displaying" to other files even when they open this file. *)

module Readback = struct
  module Displaying = Algaeff.Reader.Make (Bool)
end

open Readback

let () =
  Displaying.register_printer (function `Read -> Some "unhandled Readback.Displaying.read effect")

(* Reading back a comatch (the potential value of a neutral) as a display comatch requires degenerating the context for the non-projectable instances of its higher fields, and Degctx depends on Readback, so the implementation can't live here.  Instead it's a forward reference, set by a downstream module (Canonical_display).  It's invoked by "about" with the neutral (used as the self-variable) whose value is the comatch; ordinary readback never reaches it. *)
type readback_comatch_type = {
  rbc : 'a 'z. ('z, 'a) Ctx.t -> kinetic value -> kinetic value -> ('a, potential) term;
}

let readback_comatch : readback_comatch_type ref =
  ref { rbc = (fun _ _ _ -> fatal (Anomaly "readback_comatch not set (load Canonical_display)")) }

let rec sort_of_ty : type a z.
    ?isfunc:bool -> (z, a) Ctx.t -> View.view_type -> [ `Type | `Function | `Other ] =
 fun ?(isfunc = false) ctx -> function
  | Canonical (_, UU _, _, _) -> `Type
  | Canonical (_, Pi (_, doms, cods), _, tyargs) -> (
      match D.compare (TubeOf.inst tyargs) (CubeOf.dim doms) with
      | Neq -> fatal (Dimension_mismatch ("sort_of_ty", TubeOf.inst tyargs, CubeOf.dim doms))
      | Eq ->
          let args, newnfs = dom_vars ctx doms in
          let newctx = Ctx.invis ctx newnfs in
          let output = tyof_app cods tyargs args in
          sort_of_ty ~isfunc:true newctx (view_type output "sort_of_ty"))
  | _ -> if isfunc then `Function else `Other

(* Readback of values to terms.  Closely follows equality-testing in equal.ml, so most comments are omitted.  However, unlike equality-testing and the "readback" in theoretical NbE, this readback does *not* eta-expand functions and tuples.  It is used for (1) displaying terms to the user, who will usually prefer not to see things eta-expanded, and (2) turning values into terms so that we can re-evaluate them in a new environment, for which purpose eta-expansion is irrelevant.  There are two exceptions:

   1. When reading back at a record type that the user has marked as transparent, we eta-expand tuples.  This is chosen based on the readback type.
   2. When reading back a higher-dimensional pi-type, we eta-expand its instantiation arguments so that we can display it prettily.  This is controlled by the flag ~eta. *)

let rec readback_nf : type a z. ?eta:bool -> (z, a) Ctx.t -> normal -> (a, kinetic) term =
 fun ?(eta = false) n x -> readback_at ~eta n x.tm x.ty

(* Read back an evaluation: a Val recurses, a Realize wraps the (kinetic) realization in Realize, and an Unrealized (a genuinely stuck case tree) can't be read back as a value.  This is how we read back the result of *applying* a potential value (a case-tree lambda); for a kinetic value, apply always returns Val, so only that arm is live. *)
and readback_eval : type a z s.
    ?eta:bool -> (z, a) Ctx.t -> s evaluation -> kinetic value -> (a, s) term =
 fun ?(eta = false) ctx ev ty ->
  match ev with
  | Val v -> readback_at ~eta ctx v ty
  | Realize v -> Realize (readback_at ~eta ctx v ty)
  | Unrealized -> fatal (Anomaly "unrealized value in readback")

(* Readback is energy-polymorphic: it reads back a value of any energy 's into an ('a, 's) term.  In practice it is only ever called on a *potential* value by "about" (which reads back the forced value of a neutral); that's the only way a comatch (a no-eta struct) reaches the Codata branch and gets eta-expanded.  All other callers read back kinetic values (neutrals, etc.) and get their application spines as before. *)
and readback_at : type a z s. ?eta:bool -> (z, a) Ctx.t -> s value -> kinetic value -> (a, s) term =
 fun ?(eta = false) ctx tm ty ->
  let view = if Displaying.read () then view_term tm else tm in
  let vty = view_type ty "readback_at" in
  match (vty, view) with
  | Canonical (_, Pi (_, doms, cods), ins, tyargs), Lam ((Variables (m, mn, xs) as x), body) -> (
      let Eq = eq_of_ins_zero ins in
      let k = CubeOf.dim doms in
      let l = dim_binder body in
      match (D.compare (TubeOf.inst tyargs) k, D.compare k l) with
      | Neq, _ -> fatal (Dimension_mismatch ("reading back at pi 1", TubeOf.inst tyargs, k))
      | _, Neq -> fatal (Dimension_mismatch ("reading back at pi 2", k, l))
      | Eq, Eq ->
          let args, newnfs = dom_vars ctx doms in
          let (Plus af) = N.plus (NICubeOf.out N.zero xs) in
          let newctx = Ctx.vis ctx m mn xs newnfs af in
          let output = tyof_app cods tyargs args in
          let body = readback_eval ~eta newctx (apply tm args) output in
          Term.Lam (x, body))
  (* If eta-expansion is enabled, we do an eta-expanding readback of any term. *)
  | Canonical (_, Pi (name, doms, cods), ins, tyargs), _ when eta ->
      let Eq = eq_of_ins_zero ins in
      let newargs, newnfs = dom_vars ctx doms in
      let (Any_ctx newctx) = Ctx.variables_vis ctx name newnfs in
      let output = tyof_app cods tyargs newargs in
      (* We carry through the eta-expansion flag so that iterated pi-types will eta-expand fully. *)
      Term.Lam (name, readback_eval ~eta newctx (apply tm newargs) output)
  | ( Canonical
        (type mn m n)
        (( _,
           Codata
             (type c a et)
             ({ eta; opacity; fields; env = _; termctx = _ } : (m, n, c, a, et) codata_args),
           ins,
           _ ) :
          head * (m, n) canonical * (mn, m, n) insertion * (D.zero, mn, mn, normal) TubeOf.t),
      _ ) -> (
      match eta with
      (* A no-eta codatatype: an ordinary readback of a (kinetic) neutral here yields its application spine.  Displaying a comatch as a comatch is done by "about" via readback_comatch, which forces the neutral's potential value; it is not reached through readback_at. *)
      | Noeta -> readback_val_sorted ctx tm vty
      | Eta -> (
          (* An eta-record type.  Only kinetic values are ever read back here (records, and tuples reached via their neutral); a tuple in a case tree (a potential eta-struct) is never passed to readback for display. *)
          let dim = cod_left_ins ins in
          let fldins = ins_zero dim in
          let readback_at_record (tm : kinetic value) ty =
            match (tm, opacity) with
            (* If the term is a struct, we read back its fields.  Even though this is not technically an eta-expansion, we have to do it here rather than in readback_val because we need the record type to determine the types at which to read back the fields. *)
            | Struct { fields = tmflds; energy; ins = _; eta = _ }, _ ->
                let fields =
                  Mbwd.map
                    (* We don't need to consider the Higher case since we are kinetic. *)
                    (fun (Value.StructfieldAbwd.Entry (fld, Value.Structfield.Lower (fldtm, l))) ->
                      Term.StructfieldAbwd.Entry
                        ( fld,
                          Term.Structfield.Lower
                            ( readback_at ctx (force_eval_term fldtm)
                                (tyof_field (Ok tm) ty fld ~shuf:Trivial fldins),
                              l ) ))
                    tmflds in
                Some (Term.Struct { eta = Eta; dim; fields; energy })
            (* In addition, if the record type is transparent, or if it's translucent and the term is a tuple in a case tree, and we are reading back for display (rather than for internal typechecking purposes), we do an eta-expanding readback. *)
            | _, `Transparent l when Displaying.read () ->
                let fields =
                  Mbwd.map
                    (fun (CodatafieldAbwd.Entry
                            (type i)
                            ((fld, Lower _) : i Field.t * (i, a * n * has_eta) Codatafield.t)) ->
                      Term.StructfieldAbwd.Entry
                        ( fld,
                          Term.Structfield.Lower
                            ( readback_at ctx (field_term tm fld fldins)
                                (tyof_field (Ok tm) ty fld ~shuf:Trivial fldins),
                              l ) ))
                    fields in
                Some (Struct { eta = Eta; dim; fields; energy = Kinetic })
            | Neu { value; _ }, `Translucent l when Displaying.read () -> (
                match force_eval value with
                | Val (Struct _) ->
                    let fields =
                      Mbwd.map
                        (fun (CodatafieldAbwd.Entry
                                (type i)
                                ((fld, Lower _) : i Field.t * (i, a * n * has_eta) Codatafield.t))
                           ->
                          Term.StructfieldAbwd.Entry
                            ( fld,
                              Term.Structfield.Lower
                                ( readback_at ctx (field_term tm fld fldins)
                                    (tyof_field (Ok tm) ty fld ~shuf:Trivial fldins),
                                  l ) ))
                        fields in
                    Some (Struct { eta = Eta; dim; fields; energy = Kinetic })
                | _ -> None)
            (* If the term is not a struct and the record type is not transparent/translucent, we pass off to synthesizing readback. *)
            | _ -> None in
          let do_record (rtm : kinetic value) =
            match is_id_ins ins with
            | Some _ -> (
                match readback_at_record rtm ty with
                | Some res -> res
                | None -> readback_val_sorted ctx rtm vty)
            | None -> (
                (* A nontrivially permuted record is not a record type, but we can permute its arguments to find elements of a record type that we can then eta-expand and re-permute. *)
                let (Perm_to p) = perm_of_ins ins in
                let pinv = deg_of_perm (perm_inv p) in
                let ptm = act_value rtm pinv in
                let pty = act_ty rtm ty pinv in
                match readback_at_record ptm pty with
                | Some res -> Act (res, deg_of_perm p, (`Other, `Other))
                | None -> readback_val_sorted ctx rtm vty) in
          match view with
          | Struct { energy = Kinetic; _ } -> do_record view
          | Neu _ -> do_record view
          | _ -> readback_val_sorted ctx tm vty))
  | Canonical (_, Data { constrs; _ }, ins, tyargs), Constr (xconstr, xn, xargs) -> (
      let Eq = eq_of_ins_zero ins in
      let (Dataconstr { env; args = argtys; output = _ }) =
        Abwd.find_opt xconstr constrs <|> Anomaly "constr not found in readback" in
      match D.compare xn (TubeOf.inst tyargs) with
      | Neq -> fatal (Dimension_mismatch ("reading back constrs", xn, TubeOf.inst tyargs))
      | Eq ->
          let tyarg_args =
            TubeOf.mmap
              {
                map =
                  (fun _ [ tm ] ->
                    match view_term tm.tm with
                    | Constr (tmname, _, tmargs) ->
                        if tmname = xconstr then List.map (fun a -> CubeOf.find_top a) tmargs
                        else fatal (Anomaly "inst arg wrong constr in readback at datatype")
                    | _ -> fatal (Anomaly "inst arg not constr in readback at datatype"));
              }
              [ tyargs ] in
          Constr
            ( xconstr,
              dim_env env,
              readback_at_tel ctx env
                (List.fold_right (fun a args -> CubeOf.find_top a :: args) xargs [])
                argtys tyarg_args ))
  | _ -> readback_val_sorted ctx tm vty

and readback_val_sorted : type a z s. (z, a) Ctx.t -> s value -> View.view_type -> (a, s) term =
 fun ctx tm vty ->
  let sort = sort_of_ty ctx vty in
  readback_val ~sort ctx tm

(* The synthesizing readback only ever applies to neutrals (a kinetic value); any other value reaching it (which can only be a potential value, since other callers pass kinetic neutrals) is an anomaly. *)
and readback_val : type a z s.
    ?sort:[ `Type | `Function | `Other ] -> (z, a) Ctx.t -> s value -> (a, s) term =
 fun ?(sort = `Other) ctx x ->
  match x with
  | Neu { head; args; value; ty } -> (
      match (force_eval value, Displaying.read ()) with
      | Realize v, true -> readback_at ctx v (Lazy.force ty)
      | Val (Canonical _), _ -> readback_neu ~sort:(sort, `Canonical) ctx head args
      | _ -> readback_neu ~sort:(sort, `Other) ctx head args)
  | Lam _ -> fatal (Anomaly "unexpected lambda in synthesizing readback")
  | Struct _ -> fatal (Anomaly "unexpected struct in synthesizing readback")
  | Constr _ -> fatal (Anomaly "unexpected constr in synthesizing readback")
  | Canonical _ -> fatal (Anomaly "unexpected canonical in synthesizing readback")

and readback_neu : type a z any.
    ?sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    (z, a) Ctx.t ->
    head ->
    any apps ->
    (a, kinetic) term =
 fun ?(sort = (`Other, `Other)) ctx head apps ->
  match (apps, head) with
  | Emp, _ -> readback_head ~sort ctx head
  | Arg (apps, args, ins), _ ->
      let (To p) = deg_of_ins ins in
      Term.Act
        ( App
            ( readback_neu ~sort ctx head apps,
              CubeOf.mmap { map = (fun _ [ tm ] -> readback_nf ctx tm) } [ args ] ),
          p,
          sort )
  | Field (apps, fld, fldplus, ins), _ ->
      let (To p) = deg_of_ins ins in
      Term.Act
        (Field (readback_neu ~sort ctx head apps, fld, id_ins (cod_left_ins ins) fldplus), p, sort)
  | Inst (Emp, _, args), Pi _ when TubeOf.is_full args ->
      (* When reading back a fully instantiated higher-dimensional pi-type, we eta-expand the instantiation arguments so that it can be printed with a nice notation. *)
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ~eta:true ctx x) } [ args ] in
      Inst (readback_head ~sort ctx head, args)
  | Inst (apps, _, args), _ ->
      let args = TubeOf.mmap { map = (fun _ [ x ] -> readback_nf ctx x) } [ args ] in
      Inst (readback_neu ~sort ctx head apps, args)

and readback_head : type c z.
    ?sort:[ `Type | `Function | `Other ] * [ `Canonical | `Other ] ->
    (z, c) Ctx.t ->
    head ->
    (c, kinetic) term =
 fun ?(sort = (`Other, `Other)) ctx h ->
  match h with
  | Var { level; deg } -> (
      let x = Ctx.find_level ctx level <|> No_such_level (PLevel level) in
      match is_id_deg deg with
      | Some _ -> Var x
      | None -> Act (Var x, deg, sort))
  | Const { name; ins } -> (
      let dim = cod_left_ins ins in
      let (To perm) = deg_of_ins ins in
      let (DegExt (_, _, deg)) = comp_deg_extending (deg_zero dim) perm in
      match is_id_deg deg with
      | Some _ -> Const name
      | None -> Act (Const name, deg, sort))
  | Meta { meta; env; ins } -> (
      let tm = MetaEnv (meta, readback_env ctx env (Global.find_meta meta).termctx) in
      match is_id_ins ins with
      | Some _ -> tm
      | None ->
          let (To perm) = deg_of_ins ins in
          Act (tm, perm, sort))
  | UU m -> UU m
  | Pi (x, doms, cods) ->
      let k = CubeOf.dim doms in
      let args, newnfs = dom_vars ctx doms in
      Pi
        ( x,
          CubeOf.mmap { map = (fun _ [ dom ] -> readback_val ~sort:`Type ctx dom) } [ doms ],
          CodCube.build k
            {
              build =
                (fun fa ->
                  let (Any_ctx sctx) =
                    Ctx.variables_vis ctx (sub_variables fa x) (CubeOf.subcube fa newnfs) in
                  let sargs = CubeOf.subcube fa args in
                  readback_val ~sort:`Type sctx (apply_binder_term (BindCube.find cods fa) sargs));
            } )

and readback_at_tel : type n c a b ab z.
    (z, c) Ctx.t ->
    (n, a) env ->
    kinetic value list ->
    (a, b, ab) Telescope.t ->
    (D.zero, n, n, kinetic value list) TubeOf.t ->
    (n, (c, kinetic) term) CubeOf.t list =
 fun ctx env xs tys tyargs ->
  match (xs, tys) with
  | [], Emp -> []
  | x :: xs, Ext (_, ty, tys) ->
      let ety = eval_term env ty in
      (* Copied from check_at_tel; TODO: Factor it out *)
      let tyargtbl = Hashtbl.create 10 in
      let [ tyarg; tms; tyargs ] =
        TubeOf.pmap
          {
            map =
              (fun fa [ tyargs ] ->
                match tyargs with
                | [] -> fatal (Anomaly "missing arguments in readback_at_tel")
                | argtm :: argrest ->
                    let fa = sface_of_tface fa in
                    let argty =
                      inst
                        (eval_term (act_env env (op_of_sface fa)) ty)
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_sface fa))
                           {
                             build =
                               (fun fb ->
                                 Hashtbl.find tyargtbl
                                   (SFace_of (comp_sface fa (sface_of_tface fb))));
                           }) in
                    let argnorm = { tm = argtm; ty = argty } in
                    let argtm = readback_at ctx argtm argty in
                    Hashtbl.add tyargtbl (SFace_of fa) argnorm;
                    [ argnorm; argtm; argrest ]);
          }
          [ tyargs ] (Cons (Cons (Cons Nil))) in
      let ity = inst ety tyarg in
      TubeOf.plus_cube tms (CubeOf.singleton (readback_at ctx x ity))
      :: readback_at_tel ctx
           (Ext
              ( env,
                D.plus_zero (TubeOf.inst tyarg),
                Ok (TubeOf.plus_cube (val_of_norm_tube tyarg) (CubeOf.singleton x)) ))
           xs tys tyargs
  | _ -> fatal (Anomaly "length mismatch in equal_at_tel")

(* To readback an environment, since readback is type-directed we need the types of *all* the terms in it, which is to say its codomain context.  We store this as a Termctx since we need to evaluate and instantiate the types at the previous terms in the environment as we go. *)
and readback_env : type n a b c d.
    (a, b) Ctx.t -> (n, d) Value.env -> (c, d) termctx -> (b, n, d) Term.env =
 fun ctx env (Permute (_, envctx)) -> readback_ordered_env ctx env envctx

and readback_ordered_env : type n a b c d.
    (a, b) Ctx.t -> (n, d) Value.env -> (c, d) ordered_termctx -> (b, n, d) Term.env =
 fun ctx env envctx ->
  match envctx with
  | Emp -> Emp (dim_env env)
  | Lock envctx -> readback_ordered_env ctx env envctx
  | Ext (envctx, entry, _) -> (
      let (Plus mk) = D.plus (dim_entry entry) in
      let (Looked_up { act; op = Op (fc, fd); entry = xs }) =
        lookup_cube env mk Now (id_op (D.plus_out (dim_env env) mk)) in
      let xs = act_cube { act } (CubeOf.subcube fc xs) fd in
      match entry with
      | Vis { bindings; _ } | Invis bindings ->
          let xtytbl = Hashtbl.create 10 in
          let tmxs =
            CubeOf.mmap
              {
                map =
                  (fun fab [ tm ] ->
                    let (SFace_of_plus (_, fb, fa)) = sface_of_plus mk fab in
                    let ty = (CubeOf.find bindings fa).ty in
                    let k = dom_sface fb in
                    let ty =
                      inst
                        (eval_term (act_env env (op_of_sface fb)) ty)
                        (TubeOf.build D.zero (D.zero_plus k)
                           {
                             build =
                               (fun fc ->
                                 Hashtbl.find xtytbl (SFace_of (comp_sface fb (sface_of_tface fc))));
                           }) in
                    Hashtbl.add xtytbl (SFace_of fb) { tm; ty };
                    readback_at ctx tm ty);
              }
              [ xs ] in
          let env = remove_env env Now in
          let tmenv = readback_ordered_env ctx env envctx in
          Ext (tmenv, mk, tmxs))

(* Read back a context of values into a context of terms. *)

let readback_bindings : type a b n.
    (a, (b, n) snoc) Ctx.t -> (n, Binding.t) CubeOf.t -> (n, (b, n) snoc binding) CubeOf.t =
 fun ctx vbs ->
  CubeOf.mmap
    {
      map =
        (fun _ [ b ] ->
          match Binding.level b with
          | Some _ ->
              ({ tm = None; ty = readback_val ~sort:`Type ctx (Binding.value b).ty }
                : (b, n) snoc binding)
          | None ->
              {
                tm = Some (readback_nf ctx (Binding.value b));
                ty = readback_val ~sort:`Type ctx (Binding.value b).ty;
              });
    }
    [ vbs ]

let readback_entry : type a b f n. (a, (b, n) snoc) Ctx.t -> (f, n) Ctx.entry -> (b, f, n) entry =
 fun ctx e ->
  match e with
  | Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus } ->
      let top = Binding.value (CubeOf.find_top bindings) in
      (* Fields as illusory variables are only used when typechecking records, which have substitution dimension 0 and can have no higher fields, so as field insertion we can use the identity on zero. *)
      let fins = ins_zero D.zero in
      let fields =
        Bwv.map
          (fun (f, x) ->
            let fldty =
              readback_val ~sort:`Type ctx (tyof_field (Ok top.tm) top.ty f ~shuf:Trivial fins)
            in
            (f, x, fldty))
          fields in
      let bindings = readback_bindings ctx bindings in
      Vis { dim; plusdim; vars; bindings; hasfields; fields; fplus }
  | Invis bindings -> Invis (readback_bindings ctx bindings)

let rec readback_ordered_ctx : type a b. (a, b) Ctx.Ordered.t -> (a, b) ordered_termctx = function
  | Emp -> Emp
  | Snoc (rest, e, af) as ctx ->
      Ext (readback_ordered_ctx rest, readback_entry (Ctx.of_ordered ctx) e, af)
  | Lock ctx -> Lock (readback_ordered_ctx ctx)

let readback_ctx : type a b. (a, b) Ctx.t -> (a, b) termctx = function
  | Permute { perm; ctx; _ } -> Permute (perm, readback_ordered_ctx ctx)

(* Build the "nontrivial shuffleable" passed to tyof_higher_codatafield when computing the type of a non-projectable instance of a higher codatatype field.  The remaining dimensions 'r have been split off, the context degenerated by them (degenv, of the degenerated ambient context), and the field's shuffle is fldshuf.  Its callbacks eval-readback values and environments to move them into the degenerated context.  This is shared between checking comatches (check_higher_field) and reading back/displaying degenerate codatatypes (Unparse). *)
let higher_codatafield_shuffleable : type a b c d r h i.
    (a, b) Ctx.t ->
    c Dbwd.t ->
    (d, (c, D.zero) snoc) termctx ->
    (r, b) env ->
    r D.t ->
    (r, h, i) shuffle ->
    (r, h, i, c) shuffleable =
 fun ctx dbwd termctx degenv r fldshuf ->
  Nontrivial
    {
      dbwd;
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
                    let faenv = act_env degenv (op_of_sface (sface_of_tface fa)) in
                    let fatm = eval_term faenv ctm in
                    let faty =
                      inst (eval_term faenv cty)
                        (TubeOf.build D.zero
                           (D.zero_plus (dom_tface fa))
                           {
                             build =
                               (fun fb ->
                                 Hashtbl.find argstbl
                                   (SFace_of (comp_sface (sface_of_tface fa) (sface_of_tface fb))));
                           }) in
                    let nf = { tm = fatm; ty = faty } in
                    Hashtbl.add argstbl (SFace_of (sface_of_tface fa)) nf;
                    nf);
              } in
          { tm; ty = inst ity tyargs });
    }

(* ------------------------------------------------------------------------- *)
(* Reading back canonical types as display-only declarations, for "about".    *)
(* ------------------------------------------------------------------------- *)

(* The result of reading back a constructor's argument telescope from a value: the telescope as a term, plus the context and environment extended by fresh variables for its arguments (needed to read back the index values that follow it), and the (top-dimensional) values of those fresh argument variables in order (needed to build the constructor-as-a-function for degenerate datatypes). *)
type (_, _, _) rb_tel =
  | Rb_tel :
      ('e, 'c, 'ec) Term.tel
      * ('lev, 'ec) Ctx.t
      * (D.zero, 'ac) Value.env
      * kinetic Value.value list
      -> ('e, 'c, 'ac) rb_tel

(* Read back a (zero-dimensional) telescope of value-level types into a term-level telescope in the readback context, introducing a fresh variable for each entry. *)
let rec readback_tel : type lev e a c ac.
    (lev, e) Ctx.t -> (D.zero, a) Value.env -> (a, c, ac) Term.tel -> (e, c, ac) rb_tel =
 fun ctx env tel ->
  match tel with
  | Emp -> Rb_tel (Emp, ctx, env, [])
  | Ext (name, rty, rest) ->
      let ety = Norm.eval_term env rty in
      let newvars, newnfs = Domvars.dom_vars ctx (CubeOf.singleton ety) in
      let trty = readback_val ~sort:`Type ctx ety in
      let ctx = Ctx.cube_vis ctx name newnfs in
      let env = Value.Ext (env, D.plus_zero D.zero, Ok newvars) in
      let (Rb_tel (resttel, fctx, fenv, restvals)) = readback_tel ctx env rest in
      Rb_tel (Ext (name, trty, resttel), fctx, fenv, CubeOf.find_top newvars :: restvals)

(* The result of reading back a value-level datatype constructor: its argument telescope and, for an indexed datatype, the output type (the datatype family applied to the constructor's index values). *)
type _ rb_constr = Rb_constr : ('e, 'c, 'ec) Term.tel * ('ec, kinetic) term option -> 'e rb_constr

(* Read back a value-level datatype constructor (at dimension zero) into the readback context: its argument telescope, and, for an indexed datatype, its output type.  The output type is the stored output term (the datatype applied to the parameters and indices) evaluated at the fresh argument variables; it is shown only for indexed datatypes (the caller passes whether the datatype is indexed), matching the convention that non-indexed constructors are displayed without an output ascription. *)
let readback_dataconstr : type lev e.
    (lev, e) Ctx.t -> bool -> D.zero Value.dataconstr -> e rb_constr =
 fun ctx indexed (Dataconstr { env; args; output }) ->
  let (Rb_tel (tel, fctx, fenv, _)) = readback_tel ctx env args in
  let output =
    if indexed then Some (readback_val ~sort:`Type fctx (Norm.eval_term fenv output)) else None
  in
  Rb_constr (tel, output)

(* Read back the (higher-dimensional) function-type of a constructor of a *degenerate* (positive substitution dimension m) datatype.  The idea is that a constructor's type is morally a function type "(args) → out", and the type of the degenerate constructor is the degeneration of that function.  We can't take the degeneration of a constructor directly (there's no "tyof_constr"), but we *can* form the constructor-as-a-function "λ args. c args" together with its function-type "(args) → out", and then act on it by the pure degeneracy deg_zero m using act_ty.  Acting on a function-type instantiates its codomain at the faces of the function, which here are the lower-dimensional constructors, exactly producing e.g. "List⁽ᵉ⁾ (Id A) (cons. x₀ xs₀) (cons. x₁ xs₁)".  Reading back the result gives a higher-dimensional pi-type term, which unparses as "{x₀ x₁ : A} (x₂ : Id A x₀ x₁) … →⁽ᵉ⁾ …".  The constructor's output type "out" is the stored output term (e.g. "Vec A (suc. n)" for an indexed datatype, or the datatype itself for a non-indexed one) evaluated at the fresh argument variables. *)
let readback_degenerate_constr : type lev e m.
    (lev, e) Ctx.t -> m D.t -> Constr.t -> D.zero Value.dataconstr -> (e, kinetic) term =
 fun ctx m c (Dataconstr { env; args; output }) ->
  let (Rb_tel (tel, fctx, fenv, argvals)) = readback_tel ctx env args in
  let output_term = readback_val ~sort:`Type fctx (Norm.eval_term fenv output) in
  let argvar_terms = List.map (fun v -> readback_val fctx v) argvals in
  let cbody = Term.Constr (c, D.zero, List.map CubeOf.singleton argvar_terms) in
  let cfun = Telescope.lams tel cbody in
  let cty = Telescope.pis tel output_term in
  let cfun = Norm.eval_term (Ctx.env ctx) cfun in
  let cty = Norm.eval_term (Ctx.env ctx) cty in
  let ft = Act.act_ty cfun cty (deg_zero m) in
  readback_val ~sort:`Type ctx ft

(* Read back a degenerate constructor's function-type in a configuration with *no endpoints* (arity 0).  Then an m-cube has no proper faces, so we don't need the zero-dimensional base (which is unreachable anyway, as it would be a vertex of a faceless cube): we evaluate the constructor's function-type "(args) → output" directly in the degenerate (m-dimensional) environment that the constructor already carries.  There is still a (trivial, empty) instantiation, displayed as ".", so we instantiate the resulting m-dimensional function-type at the empty boundary tube before reading back.  Since the cube has no proper faces, the tube's builder is never called. *)
let readback_degenerate_constr_uninst : type lev e m.
    (lev, e) Ctx.t -> m Value.dataconstr -> (e, kinetic) term =
 fun ctx (Dataconstr { env; args; output }) ->
  let m = dim_env env in
  let ft = Norm.eval_term env (Telescope.pis args output) in
  let boundary =
    TubeOf.build D.zero (D.zero_plus m)
      { build = (fun _ -> fatal (Anomaly "arity-0 cube has no boundary faces")) } in
  readback_val ~sort:`Type ctx (Norm.inst ft boundary)

(* Build the display node for a value-level (zero-dimensional) datatype: each constructor as a telescope of arguments plus, for an indexed datatype, its output type. *)
let data_display_value : type lev e.
    (lev, e) Ctx.t -> bool -> (Constr.t, D.zero Value.dataconstr) Abwd.t -> e Term.canonical_display
    =
 fun ctx indexed constrs ->
  Data_display
    (Abwd.mapi
       (fun _ dc ->
         let (Rb_constr (tel, output)) = readback_dataconstr ctx indexed dc in
         Term.Tel_constr (tel, output))
       constrs)

(* Build the display node for a value-level *degenerate* (positive substitution dimension) datatype: each constructor as its (higher-dimensional) function-type.  Normally (arity ≥ 1) we obtain the underlying zero-dimensional datatype d0 as a vertex of the degenerate one (a boundary face of its degenerate-universe type) and read back each constructor's function-type via readback_degenerate_constr, which instantiates the codomain at the lower-dimensional constructors.  In a configuration with no endpoints (arity 0) the cube has no vertex, but it also has no boundary to instantiate, so we read back each constructor's function-type directly in its degenerate environment via readback_degenerate_constr_uninst. *)
let degenerate_data_display : type a b m j ij.
    (a, b) Ctx.t -> kinetic Value.value -> (m, j, ij) Value.data_args -> b Term.canonical_display =
 fun ctx tm data_args ->
  let pi_constrs : type d.
      (Constr.t -> d Value.dataconstr -> (b, kinetic) term) ->
      (Constr.t, d Value.dataconstr) Abwd.t ->
      b Term.canonical_display =
   fun readback_constr constrs ->
    Data_display (Abwd.mapi (fun c dc -> Term.Pi_constr (readback_constr c dc)) constrs) in
  (* The caller has already forced tm to a Canonical datatype, so its type is a (degenerate) universe. *)
  match tm with
  | Value.Neu { ty; _ } -> (
      match View.view_type (Lazy.force ty) "degenerate_data_display" with
      | Canonical (_, UU mm, ins0, boundary) -> (
          let Eq = eq_of_ins_zero ins0 in
          (* The underlying zero-dimensional datatype is a vertex of the degenerate one, recovered from the boundary faces of its (degenerate-universe) type.  In arity 0 there is no vertex; then there is also no boundary, so we display directly from the degenerate environment. *)
          let dom = TubeOf.plus_cube (val_of_norm_tube boundary) (CubeOf.singleton tm) in
          match vertex mm with
          | None ->
              pi_constrs (fun _ dc -> readback_degenerate_constr_uninst ctx dc) data_args.constrs
          | Some v -> (
              let d0 = CubeOf.find dom v in
              match View.view_type d0 "degenerate_data_display d0" with
              | Canonical (_, Data d0_args, _, _) -> (
                  match D.compare_zero d0_args.dim with
                  | Pos _ -> fatal (Anomaly "boundary vertex of degenerate datatype is not 0-dim")
                  | Zero ->
                      pi_constrs
                        (fun c dc -> readback_degenerate_constr ctx mm c dc)
                        d0_args.constrs)
              | _ -> fatal (Anomaly "boundary vertex of degenerate datatype is not a datatype")))
      | _ -> fatal (Anomaly "type of degenerate datatype is not a universe"))
  | _ -> fatal (Anomaly "degenerate datatype value is not neutral")
