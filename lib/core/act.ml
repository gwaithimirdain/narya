open Util
open Perhaps
open Dim
open Reporter
open Term
open Value
open View

(* Operator actions on values.  Unlike substitution, operator actions take a *value* as input (and produces another value). *)

(* Since values don't have a statically specified dimension, we have to act on them by an *arbitrary* degeneracy, which means that in many places we have to check dynamically that the dimensions either match or can be extended to match.  This function encapsulates that. *)
let deg_plus_to : type m n nk. on:string -> ?err:Code.t -> (m, n) deg -> nk D.t -> nk deg_of =
 fun ~on ?err s nk ->
  match factor nk (cod_deg s) with
  | None -> fatal (Option.value err ~default:(Invalid_degeneracy_action (on, nk, cod_deg s)))
  | Some (Factor nk) ->
      let (Plus mk) = D.plus (D.plus_right nk) in
      let sk = deg_plus s nk mk in
      Of sk

type (_, _) act_inst_canonical =
  | Act_inst_canonical : ('m, 'k, 'mk, 'e, 'n) inst_canonical -> ('k, 'n) act_inst_canonical

type (_, _, _) acted_instargs =
  | Acted_instargs :
      ('m, 'n) deg * ('m, 'j, 'mj, normal) TubeOf.t * ('m D.pos, 'p) Perhaps.t
      -> ('n, 'j, 'p) acted_instargs

type _ ty_acted_instargs =
  | Ty_acted_instargs : ('m, 'n) deg * (D.zero, 'm, 'm, normal) TubeOf.t -> 'n ty_acted_instargs

(* Act on a cube of objects *)

type ('a, 'b) actor = { act : 'm 'n. 'a -> ('m, 'n) deg -> 'b }

let act_cube : type a b m n. (a, b) actor -> (n, a) CubeOf.t -> (m, n) deg -> (m, b) CubeOf.t =
 fun actor xs fa ->
  CubeOf.build (dom_deg fa)
    {
      build =
        (fun fb ->
          let (Op (fd, fc)) = deg_sface fa fb in
          actor.act (CubeOf.find xs fd) fc);
    }

module Act = struct
  (* When acting on a cube of variables that's at least partially split up into ordinary variables, we have a problem if the degeneracy mixes up the dimensions that are ordinary with the dimensions that are cube.  We could get around this by storing an 'insertion' rather than a D.plus in a 'variables', but we wouldn't be able to *use* that usefully anywhere, since there's no way to create a partially-cube variable in syntax.  So instead, if the dimensions get mixed up we just give up the split and make it fully-cube using only the previous top variable.  *)
  let act_variables : type m n. n variables -> (m, n) deg -> m variables =
   fun (Variables (_, nk, vars)) s ->
    match deg_perm_of_plus nk s with
    | None_deg_perm_of_plus ->
        let m = dom_deg s in
        Variables (m, D.plus_zero m, NICubeOf.singleton (NICubeOf.find_top vars))
    (* If the degeneracy doesn't mix up the ordinary and cube dimensions, it still might permute the ordinary ones.  I'm not positive that it makes sense to throw away the degeneracy part here and the permutation part below, but this is the best I can think of.  If it doesn't end up making sense, we may have to revert to making it fully-cube as above. *)
    | Deg_perm_of_plus (ml, s, p) ->
        let m = dom_deg s in
        let module Build = NICubeOf.Traverse (struct
          type 'acc t = unit
        end) in
        let (Wrap (vars, _)) =
          Build.build_left (D.plus_right ml)
            {
              build =
                (fun fa () ->
                  let (Face (fb, _)) = perm_sface p fa in
                  Fwrap (NFamOf (NICubeOf.find vars fb), ()));
            }
            () in
        Variables (m, ml, vars)

  (* Acting on a binder and on other sorts of closures will be unified by the function 'act_closure', but its return value involves an existential type, so it has to be a GADT. *)
  type (_, _, _) act_closure =
    | Act_closure : ('m, 'a) env * ('mn, 'm, 'n) insertion -> ('a, 'mn, 'n) act_closure

  let rec act_value : type m n status. status value -> (m, n) deg -> status value =
   fun v s ->
    match v with
    | Neu { head; args; value; ty = (lazy ty) } ->
        (* We act on the applications from the outside (last) to the inside, since the degeneracy has to be factored and may leave neutral insertions behind.  The resulting inner degeneracy then acts on the head. *)
        let Any_deg s', args = act_apps args s in
        let head = act_head head s' in
        (* We act on the value separately with the original s, since it is a "value" of the entire application spine, not just the head. *)
        let value = act_lazy_eval value s in
        (* And we "act" on the type with the other kind of action that permutes the instantiated arguments, and by the original s since it is the type of the entire application spine. *)
        let ty = lazy (act_ty v ty s) in
        Neu { head; args; value; ty }
    | Lam (x, body) ->
        let (Of fa) = deg_plus_to s (dim_binder body) ~on:"lambda" in
        Lam (act_variables x fa, act_binder body fa)
    | Struct
        (type p k pk et)
        ((fields, ins, energy) :
          (p * status * et) Value.StructfieldAbwd.t * (pk, p, k) insertion * status energy) ->
        let (Insfact_comp_ext
               (type q l ql j z)
               ((deg0, new_ins, _, _) :
                 (q, p) deg * (ql, q, l) insertion * (k, j, l) D.plus * (m, z, ql) D.plus)) =
          insfact_comp_ext ins s in
        let fields = act_structfield_abwd deg0 fields in
        Struct (fields, new_ins, energy)
    | Constr (name, dim, args) ->
        let (Of fa) = deg_plus_to s dim ~on:"constr" in
        Constr
          ( name,
            dom_deg fa,
            List.map (fun tm -> act_cube { act = (fun x s -> act_value x s) } tm fa) args )
    | Canonical ic ->
        let (Act_inst_canonical newic) = act_inst_canonical ic s in
        Canonical newic

  and act_inst_canonical : type m k mk e n a b.
      (m, k, mk, e, n) inst_canonical -> (a, b) deg -> (k, n) act_inst_canonical =
   fun { canonical; tyargs; ins } s ->
    let (Acted_instargs (fa, new_tyargs, None)) = act_instargs tyargs s None in
    let fb = deg_plus fa (TubeOf.plus tyargs) (TubeOf.plus new_tyargs) in
    let (Insfact_comp (fc, new_ins)) = insfact_comp ins fb in
    let new_c = act_canonical canonical fc in
    Act_inst_canonical { canonical = new_c; tyargs = new_tyargs; ins = new_ins }

  and act_structfield : type p q i status et.
      (q, p) deg -> (i, p * status * et) Structfield.t -> (i, q * status * et) Structfield.t =
   fun deg0 sfld ->
    match sfld with
    (* For a lower structfield, we just act in a straightforward way on each (lazy) value. *)
    | Lower (v, l) -> Lower (act_lazy_eval v deg0, l)
    | Higher (lazy { vals; intrinsic; plusdim; env; deg = deg1; terms }) ->
        Higher (lazy (act_higher_structfield deg0 vals intrinsic plusdim env deg1 terms))

  and act_higher_structfield : type m n mn a p q i.
      (q, p) deg ->
      (p, i, potential lazy_eval option) InsmapOf.t ->
      i D.t ->
      (m, n, mn) D.plus ->
      (m, a) env ->
      (p, mn) deg ->
      (n, i, a) PlusPbijmap.t ->
      (m, n, mn, q, i, a) Structfield.higher_data =
   fun deg0 vals intrinsic plusdim env deg1 terms ->
    (* Now we want to change p to q by acting by fa : (q, p) deg.  We'll keep almost everything the same and simply compose deg with fa.  The sticky bit is to update vals, which has to become an Insmap with evaluation dimension q rather than p. *)
    let deg = comp_deg deg1 deg0 in
    let vals =
      InsmapOf.build (dom_deg deg0) intrinsic
        {
          build =
            (fun (type s) (ins : (q, s, i) insertion) ->
              (* First we unfactor this q-insertion through deg0 to get a partial bijection from p to i. *)
              let (Deg_comp_ins
                     (type s2 r2 h2)
                     ((ins2, shuf2, deg2) :
                       (p, s2, h2) insertion * (r2, h2, i) shuffle * (s, s2) deg)) =
                deg_comp_ins deg0 ins in
              let r2 = left_shuffle shuf2 in
              (* If this partial bijection is itself just an insertion, then we can simply use it as an index into the old vals and act in a simple way, as we did for lower structfields. *)
              match D.compare_zero r2 with
              | Zero ->
                  let Eq = eq_of_zero_shuffle shuf2 in
                  (* Note we have to act by deg2 here, not by deg0, since the field *values* only have the corresponding 'result dimension. *)
                  Option.map (fun v -> act_lazy_eval v deg2) (InsmapOf.find ins2 vals)
              | Pos _s -> (
                  (* Otherwise, we have to look into the 'terms' to find something to evaluate.  We start by further unfactoring through the composite degeneracy 'deg' and 'plusdim' to get down to the original record dimension 'n and evaluation dimension 'm.  *)
                  let (Deg_comp_ins
                         (type s3 r3 h3)
                         ((ins3, shuf3, deg3) :
                           (mn, s3, h3) insertion * (r3, h3, i) shuffle * (s, s3) deg)) =
                    deg_comp_ins deg ins in
                  (* The dimensions that disappear in this degeneracy, and hence will have to be added back in, are those added by the degeneracy deg3 (s - s3) and those in the remaining dimensions r3. *)
                  let (Unplus_pbij
                         (type s4 h4 r4 r34 t)
                         ((ins4, shuf4, rr, mtr, _ts) :
                           (n, s4, h4) insertion
                           * (r34, h4, i) shuffle
                           * (r3, r4, r34) shuffle
                           * (m, t, r4) insertion
                           * (t, s4, s3) D.plus)) =
                    unplus_pbij (dim_env env) plusdim ins3 shuf3 in
                  match PlusPbijmap.find (Pbij (ins4, shuf4)) terms with
                  | PlusFam None -> None
                  | PlusFam
                      (type ra)
                      (Some (ra, tm) : ((r34, a, ra) Plusmap.t * (ra, potential) term) option) ->
                      (* Now the game is to build a degeneracy that we can apply to the m-dimensional environment 'env' so that we can shift it by the plusmap 'ra' and evaluate the term 'tm'.  (Note that 'tm' is s4-dimensional as that is the result dimension of the pbij that indexes it.)  That means we need to get an environment whose dimension is something+r34.  We start by adding r3, and then apply a bunch of permutations.
                             m + r3
                             ≅ (t + r4) + r3    (mtr)
                             ≅ t + (r4 + r3)
                             ≅ t + (r3 + r4)
                             ≅ t + r34          (rr)
                          *)
                      let m = dim_env env in
                      let r3 = left_shuffle rr in
                      let (Plus mr3) = D.plus r3 in
                      let plusr3 = plus_deg m (D.plus_zero m) mr3 (deg_zero r3) in
                      let env1 = act_env env (op_of_deg plusr3) in
                      (* env1 has dimension m + r3 *)
                      let r4 = cod_right_ins mtr in
                      let (Plus tr4) = D.plus r4 in
                      let mtrp = deg_of_perm (perm_inv (perm_of_ins_plus mtr tr4)) in
                      let (Plus tr4_r3) = D.plus r3 in
                      let env2 = act_env env1 (op_of_deg (deg_plus mtrp mr3 tr4_r3)) in
                      (* env2 has dimension (t + r4) + r3 *)
                      let (Plus r4r3) = D.plus r3 in
                      let (Plus r3r4) = D.plus r4 in
                      let t_r4r3 = D.plus_assocr tr4 r4r3 tr4_r3 in
                      let (Plus t_r3r4) = D.plus (D.plus_out r3 r3r4) in
                      let rrswap = swap_deg r3r4 r4r3 in
                      let t = cod_left_ins mtr in
                      let env3 = act_env env2 (op_of_deg (plus_deg t t_r4r3 t_r3r4 rrswap)) in
                      (* env3 has dimension t + (r3 + r4). *)
                      let r34 = out_shuffle rr in
                      let (Plus t_r34) = D.plus r34 in
                      let drr = plus_deg t t_r3r4 t_r34 (deg_of_shuffle rr r3r4) in
                      let env4 = act_env env3 (op_of_deg drr) in
                      (* env4 has dimension t + r34 *)
                      let env5 = Shift (env4, t_r34, ra) in
                      (* env5 has dimension t.  So when we evaluate the s4-dimensional term 'tm' in this environment, we get an object of dimension t + s4, which is equal to s3.  Therefore, we can act on it by deg3 to get an s-dimensional object, which is what we want. *)
                      Some (act_lazy_eval (lazy_eval env5 tm) deg3)));
        } in
    { vals; intrinsic; plusdim; env; deg; terms }

  and act_structfield_abwd : type p q status et.
      (q, p) deg -> (p * status * et) StructfieldAbwd.t -> (q * status * et) StructfieldAbwd.t =
   fun deg fields ->
    Mbwd.mmap
      (fun [ StructfieldAbwd.Entry (fld, sfld) ] ->
        StructfieldAbwd.Entry (fld, act_structfield deg sfld))
      [ fields ]

  and act_evaluation : type m n s. s evaluation -> (m, n) deg -> s evaluation =
   fun tm s ->
    match tm with
    | Unrealized -> Unrealized
    | Realize tm -> Realize (act_value tm s)
    | Val tm -> Val (act_value tm s)

  and act_canonical : type m n i mi. (n, i) canonical -> (m, n) deg -> (m, i) canonical =
   fun tm fa ->
    match tm with
    | UU _ -> UU (dom_deg fa)
    | Pi (x, doms, cods) ->
        let doms', cods' = act_pi (doms, cods) fa in
        Pi (x, doms', cods')
    | Data { dim = _; tyfam; indices; constrs; discrete } ->
        let tyfam = ref (Option.map (fun x -> lazy (act_normal (Lazy.force x) fa)) !tyfam) in
        let indices =
          Fillvec.map (fun ixs -> act_cube { act = (fun x s -> act_normal x s) } ixs fa) indices
        in
        let constrs = Abwd.map (fun c -> act_dataconstr c fa) constrs in
        Data { dim = dom_deg fa; tyfam; indices; constrs; discrete }
    | Codata { eta; opacity; env; termctx; fields } ->
        Codata { eta; opacity; env = act_env env (op_of_deg fa); termctx; fields }

  and act_dataconstr : type m n i. (n, i) dataconstr -> (m, n) deg -> (m, i) dataconstr =
   fun (Dataconstr { env; args; indices }) s ->
    let env = act_env env (op_of_deg s) in
    Dataconstr { env; args; indices }

  (* act_closure and act_binder assume that the degeneracy has exactly the correct codomain.  So if it doesn't, the caller should call deg_plus_to first. *)
  and act_closure : type mn m n a kn.
      (m, a) env -> (mn, m, n) insertion -> (kn, mn) deg -> (a, kn, n) act_closure =
   fun env ins fa ->
    let (Insfact_comp (fc, ins)) = insfact_comp ins fa in
    Act_closure (act_env env (op_of_deg fc), ins)

  and act_binder : type mn kn s. (mn, s) binder -> (kn, mn) deg -> (kn, s) binder =
   fun (Bind { env; ins; body }) fa ->
    let (Act_closure (env, ins)) = act_closure env ins fa in
    Bind { env; ins; body }

  and act_normal : type a b. normal -> (a, b) deg -> normal =
   fun { tm; ty } s -> { tm = act_value tm s; ty = act_ty tm ty s }

  (* When acting on a neutral or normal, we also need to specify the type of the output.  This *isn't* act_value on the original type; instead the type is required to be fully instantiated and the operator acts on the *instantiated* dimensions, in contrast to how act_value on an instantiation acts on the *uninstantiated* dimensions (as well as the instantiated term).  This function computes this "type of acted terms".  In general, it has to be passed the term as well as the type because the instantiation of the result may involve that term, e.g. if x : A then refl x : Id A x x; but we allow that term to be omitted in case the degeneracy is a pure symmetry in which case this doesn't happen. *)
  and gact_ty : type a b.
      ?err:Code.t -> kinetic value option -> kinetic value -> (a, b) deg -> kinetic value =
   fun ?err tm tmty s ->
    (* We have to normalize the type in order to be sure of exposing the instantiations.  But we can't use view_type, because that discards information and we need to reconstruct the acted type. *)
    match view_term tmty with
    | Lam _ | Struct _ | Constr _ -> fatal (Anomaly "invalid term: not a type to act on")
    (* The type must be UU 0, since this IS a TYPE (that has elements).  But we don't bother checking that it already was. *)
    | Neu { head; args; value; ty = _ } ->
        (* Pull off the instantiation, perhaps empty, from the end of the arguments. *)
        let base_args, Full_tube inst_args =
          match args with
          | Inst (base_args, _, inst_args) -> (
              match D.compare_zero (TubeOf.uninst inst_args) with
              | Zero ->
                  let Eq =
                    D.plus_uniq (TubeOf.plus inst_args) (D.zero_plus (TubeOf.inst inst_args)) in
                  (base_args, (TubeOf.Full_tube inst_args : normal TubeOf.full))
              | Pos _ -> fatal (Dimension_mismatch ("act_ty", TubeOf.uninst inst_args, D.zero)))
          | Arg _ -> (args, TubeOf.Full_tube (TubeOf.empty D.zero))
          | Field _ -> (args, TubeOf.Full_tube (TubeOf.empty D.zero))
          | Emp -> (args, TubeOf.Full_tube (TubeOf.empty D.zero)) in
        let (Ty_acted_instargs (fa, new_inst_args)) = gact_ty_instargs ?err tm tmty inst_args s in
        (* Now we act on the rest of the spine in the ordinary way. *)
        let Any_deg fa, new_base_args = act_apps base_args fa in
        let head = act_head head fa in
        (* And put back on the instantiation, if it's nontrivial.  (It should always be nontrivial unless 's' was the identity degeneracy of D.zero, which should be prevented by short-circuiting.) *)
        let (Any args) =
          match D.compare_zero (TubeOf.inst new_inst_args) with
          | Zero -> Any base_args
          | Pos k -> Any (Inst (new_base_args, k, new_inst_args)) in
        (* Since we've normalized the type already, its 'value' can't be a 'Realize'; it must be a Val Canonical or an Unrealized.  In the Canonical case, we act on its instantiation arguments (which should really be the same arguments) in the same way. *)
        let value =
          match force_eval value with
          | Realize _ -> fatal (Anomaly "Realize in normalized type in act_ty")
          | Unrealized -> ready Unrealized
          | Val (Canonical { canonical = c; tyargs = ctyargs; ins }) -> (
              match D.compare_zero (TubeOf.uninst ctyargs) with
              | Zero ->
                  let Eq = D.plus_uniq (TubeOf.plus ctyargs) (D.zero_plus (TubeOf.inst ctyargs)) in
                  let (Ty_acted_instargs (fa, new_ctyargs)) =
                    gact_ty_instargs ?err tm tmty ctyargs s in
                  let (Insfact_comp (fc, new_ins)) = insfact_comp ins fa in
                  let new_c = act_canonical c fc in
                  ready (Val (Canonical { canonical = new_c; tyargs = new_ctyargs; ins = new_ins }))
              | Pos _ -> fatal (Anomaly "non fully instantiated type in act_ty"))
          | Val _ -> fatal (Anomaly "non-canonical potential value in act_ty") in
        let ty = lazy (universe D.zero) in
        Neu { head; args; value; ty }

  (* Subroutine of gact_ty that acts on the instantiation arguments of a type, keeping them a full tube. *)
  and gact_ty_instargs : type a b n.
      ?err:Code.t ->
      kinetic value option ->
      kinetic value ->
      (D.zero, n, n, normal) TubeOf.t ->
      (a, b) deg ->
      n ty_acted_instargs =
   fun ?err tm tmty inst_args s ->
    (* We check that the degeneracy can be extended to match the instantiation dimension.  If this fails, it is sometimes a bug, but sometimes a user error, e.g. when trying to symmetrize a 1-dimensional thing.  So we allow the caller to provide the error code. *)
    let (Of fa) = deg_plus_to s (TubeOf.inst inst_args) ?err ~on:"instantiated type" in
    (* We build the new arguments by factorization and action.  Note that the one missing face would be "act_value tm s", which would be an infinite loop in case tm is a neutral.  (Hence why we can't just call act_cube and then take the boundary.) *)
    let new_inst_args =
      TubeOf.build D.zero
        (D.zero_plus (dom_deg fa))
        {
          build =
            (fun fb ->
              let (Op (fd, fc)) = deg_sface fa (sface_of_tface fb) in
              let ftm =
                (* The arguments of a full instantiation are missing only the top face, which is filled in by the term belonging to it. *)
                match (pface_of_sface fd, tm) with
                | `Proper fd, _ -> TubeOf.find inst_args fd
                | `Id Eq, Some tm -> { tm; ty = tmty }
                | `Id _, None ->
                    fatal (Anomaly "term missing in instantiated act_ty by non-symmetry") in
              act_normal ftm fc);
        } in
    Ty_acted_instargs (fa, new_inst_args)

  (* Version of gact_ty that always takes the term value. *)
  and act_ty : type a b.
      ?err:Code.t -> kinetic value -> kinetic value -> (a, b) deg -> kinetic value =
   fun ?err tm tmty s -> gact_ty ?err (Some tm) tmty s

  (* Action on a head *)
  and act_head : type a b. head -> (a, b) deg -> head =
   fun ne s ->
    match ne with
    (* To act on a variable, we just accumulate the delayed action. *)
    | Var { level; deg } ->
        let (DegExt (_, _, deg)) = comp_deg_extending deg s in
        Var { level; deg }
    (* To act on a constant, we push as much of the degeneracy through the insertion as possible.  The actual degeneracy that gets pushed through doesn't matter, since it just raises the constant to an even higher dimension, and that dimension is stored in the insertion. *)
    | Const { name; ins } ->
        let (Insfact_comp_ext (_, ins, _, _)) = insfact_comp_ext ins s in
        Const { name; ins }
    (* Acting on a metavariable is similar to a constant, but now the inner degeneracy acts on the stored environment. *)
    | Meta { meta; env; ins } ->
        let (Insfact_comp_ext (deg, ins, _, _)) = insfact_comp_ext ins s in
        Meta { meta; env = act_env env (op_of_deg deg); ins }
    | UU nk ->
        let (Of fa) = deg_plus_to s nk ~on:"universe head" in
        UU (dom_deg fa)
    | Pi (x, doms, cods) ->
        let (Of fa) = deg_plus_to s (CubeOf.dim doms) ~on:"pi-type head" in
        let doms', cods' = act_pi (doms, cods) fa in
        Pi (x, doms', cods')

  and act_pi : type m n.
      (n, kinetic value) CubeOf.t * (n, unit) BindCube.t ->
      (m, n) deg ->
      (m, kinetic value) CubeOf.t * (m, unit) BindCube.t =
   fun (doms, cods) fa ->
    let mi = dom_deg fa in
    let doms' = act_cube { act = (fun x s -> act_value x s) } doms fa in
    let cods' =
      BindCube.build mi
        {
          build =
            (fun fb ->
              let (Op (fc, fd)) = deg_sface fa fb in
              act_binder (BindCube.find cods fc) fd);
        } in
    (doms', cods')

  (* Action on a Bwd of applications (each of which is just the argument and its boundary).  Pushes the degeneracy past the stored insertions, factoring it each time and leaving an appropriate insertion on the outside.  Also returns the innermost degeneracy, for acting on the head with. *)
  and act_apps : type a b any. any apps -> (a, b) deg -> any_deg * any apps =
   fun apps s ->
    match apps with
    | Emp -> (Any_deg s, Emp)
    (* To act on an application, we compose the acting degeneracy with the delayed insertion, factor the result into a new insertion to leave outside and a smaller degeneracy to push in, and push the smaller degeneracy action into the application, acting on the function/struct. *)
    | Arg (rest, args, ins) ->
        let (Insfact_comp_ext (fa, new_ins, _, _)) = insfact_comp_ext ins s in
        (* In the function case, we also act on the arguments by factorization. *)
        let new_arg = act_cube { act = (fun x s -> act_normal x s) } args fa in
        let new_s, new_rest = act_apps rest fa in
        (new_s, Arg (new_rest, new_arg, new_ins))
    | Field (rest, fld, fldplus, ins) ->
        let (Insfact_comp_ext (fa, new_ins, _, _)) = insfact_comp_ext ins s in
        (* Note that we don't need to change the degeneracy, since it can be extended on the right as needed. *)
        let (Plus new_fldplus) = D.plus (D.plus_right fldplus) in
        let new_s, new_rest = act_apps rest fa in
        (new_s, Field (new_rest, fld, new_fldplus, new_ins))
    | Inst (rest, dim, args) ->
        let (Acted_instargs (fa, new_args, None)) = act_instargs args s None in
        let new_s, new_rest = act_apps rest fa in
        (new_s, Inst (new_rest, dim, new_args))

  and act_instargs : type a b n j nj p.
      (n, j, nj, normal) TubeOf.t ->
      (a, b) deg ->
      (n D.pos, p) Perhaps.t ->
      (n, j, p) acted_instargs =
   fun args s np ->
    (* The action on an instantiation instantiates the same dimension j, but the leftover dimensions are now the domain of the degeneracy. *)
    let j = TubeOf.inst args in
    let n = TubeOf.uninst args in
    let (Of fa) = deg_plus_to s n ~on:"instantiation" in
    let nj = TubeOf.plus args in
    let m = dom_deg fa in
    let (Plus mj) = D.plus j in
    (* The new arguments are obtained by factoring and acting on appropriate original arguments *)
    let args =
      TubeOf.build m mj
        {
          build =
            (fun fed ->
              let (PFace_of_plus (_, fb, fd)) = pface_of_plus fed in
              let (Op (fe, fs)) = deg_sface fa fb in
              let (Plus q) = D.plus (dom_tface fd) in
              act_normal (TubeOf.find args (sface_plus_pface fe nj q fd)) fs);
        } in
    match np with
    | None -> Acted_instargs (fa, args, None)
    | Some np -> Acted_instargs (fa, args, Some (pos_deg np fa))

  and act_lazy_eval : type s m n. s lazy_eval -> (m, n) deg -> s lazy_eval =
   fun lev s ->
    match !lev with
    | Deferred_eval (env, tm, ins, apps) ->
        let Any_deg s, apps = act_apps apps s in
        let (Insfact_comp_ext (fa, ins, _, _)) = insfact_comp_ext ins s in
        ref (Deferred_eval (act_env env (op_of_deg fa), tm, ins, apps))
    | Deferred (tm, s', apps) ->
        let Any_deg s, apps = act_apps apps s in
        let (DegExt (_, _, fa)) = comp_deg_extending s' s in
        ref (Deferred (tm, fa, apps))
    | Ready tm -> ref (Deferred ((fun () -> tm), s, Emp))
end

let short_circuit : type m n a. (m, n) deg -> a -> ((m, n) deg -> a) -> a =
 fun s x act ->
  match is_id_deg s with
  | Some _ -> x
  | None -> act s

let act_value tm s = short_circuit s tm (Act.act_value tm)
let act_normal tm s = short_circuit s tm (Act.act_normal tm)
let gact_ty ?err tm ty s = short_circuit s ty (Act.gact_ty ?err tm ty)
let act_ty ?err tm ty s = short_circuit s ty (Act.act_ty ?err tm ty)
let act_evaluation ev s = short_circuit s ev (Act.act_evaluation ev)
let act_lazy_eval v s = short_circuit s v (Act.act_lazy_eval v)

let act_value_cube : type a s m n.
    (a -> s value) -> (n, a) CubeOf.t -> (m, n) deg -> (m, s value) CubeOf.t =
 fun force xs s -> act_cube { act = (fun x s -> act_value (force x) s) } xs s

(* Like apply_lazy for fields.  Was deferred to here since it requires pushing the insertion through with act. *)
let field_lazy : type s n t i. s lazy_eval -> i Field.t -> (n, t, i) insertion -> s lazy_eval =
 fun lev fld fldins ->
  let n, k = (cod_left_ins fldins, cod_right_ins fldins) in
  let (Plus nk) = D.plus k in
  let p = deg_of_perm (perm_inv (perm_of_ins_plus fldins nk)) in
  match !(act_lazy_eval lev p) with
  | Deferred_eval (env, tm, ins, apps) ->
      ref (Deferred_eval (env, tm, ins, Field (apps, fld, nk, ins_zero n)))
  | Deferred (tm, ins, apps) -> ref (Deferred (tm, ins, Field (apps, fld, nk, ins_zero n)))
  | Ready tm -> ref (Deferred ((fun () -> tm), id_deg D.zero, Field (Emp, fld, nk, ins_zero n)))
