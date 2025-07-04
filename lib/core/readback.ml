open Util
open Tbwd
open Reporter
open Dim
open Term
open Value
open Domvars
open Act
open Norm
open Printable
module Binding = Ctx.Binding

(* Wrapping the "Displaying" module in another module called "Readback" and opening that module allows us to refer to the module as just "Displaying" here, but exports it as "Readback.Displaying" to other files even when they open this file. *)

module Readback = struct
  module Displaying = Algaeff.Reader.Make (Bool)
end

open Readback

let () =
  Displaying.register_printer (function `Read -> Some "unhandled Readback.Displaying.read effect")

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

and readback_at : type a z.
    ?eta:bool -> (z, a) Ctx.t -> kinetic value -> kinetic value -> (a, kinetic) term =
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
          let body = readback_at ~eta newctx (apply_term tm args) output in
          Term.Lam (x, body))
  (* If eta-expansion is enabled, we do an eta-expanding readback of any term. *)
  | Canonical (_, Pi (name, doms, cods), ins, tyargs), tm when eta ->
      let Eq = eq_of_ins_zero ins in
      let newargs, newnfs = dom_vars ctx doms in
      let (Any_ctx newctx) = Ctx.variables_vis ctx name newnfs in
      let output = tyof_app cods tyargs newargs in
      (* We carry through the eta-expansion flag so that iterated pi-types will eta-expand fully. *)
      Term.Lam (name, readback_at ~eta newctx (apply_term tm newargs) output)
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
      match (eta, fields) with
      | Eta, (fields : (a * n * has_eta) Term.CodatafieldAbwd.t) -> (
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
          match is_id_ins ins with
          | Some _ -> (
              match readback_at_record tm ty with
              | Some res -> res
              | None -> readback_val_sorted ctx tm vty)
          | None -> (
              (* A nontrivially permuted record is not a record type, but we can permute its arguments to find elements of a record type that we can then eta-expand and re-permute. *)
              let (Perm_to p) = perm_of_ins ins in
              let pinv = deg_of_perm (perm_inv p) in
              let ptm = act_value tm pinv in
              let pty = act_ty tm ty pinv in
              match readback_at_record ptm pty with
              | Some res -> Act (res, deg_of_perm p, (`Other, `Other))
              | None -> readback_val_sorted ctx tm vty))
      | Noeta, _ -> readback_val_sorted ctx tm vty)
  | Canonical (_, Data { constrs; _ }, ins, tyargs), Constr (xconstr, xn, xargs) -> (
      let Eq = eq_of_ins_zero ins in
      let (Dataconstr { env; args = argtys; indices = _ }) =
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

and readback_val_sorted : type a z.
    (z, a) Ctx.t -> kinetic value -> View.view_type -> (a, kinetic) term =
 fun ctx tm vty ->
  let sort = sort_of_ty ctx vty in
  readback_val ~sort ctx tm

and readback_val : type a z.
    ?sort:[ `Type | `Function | `Other ] -> (z, a) Ctx.t -> kinetic value -> (a, kinetic) term =
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
