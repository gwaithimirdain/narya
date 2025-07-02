open Bwd
open Dim
open Core
open Value
open Norm
open Check
open Notation
open Postprocess
open Reporter

let def trie name ty tm =
  let ctx = Ctx.empty in
  let const = Constant.make Compunit.basic in
  let trie = Scope.Mod.union_singleton ~prefix:Emp trie ([ name ], ((`Constant const, None), ())) in
  Scope.run ~init_visible:trie @@ fun () ->
  let (Wrap pty) = Parse.Term.final (Parse.Term.parse (`String { content = ty; title = None })) in
  let rty = process Emp pty in
  let cty = check (Kinetic `Nolet) ctx rty (universe D.zero) in
  let ety = eval_term (Ctx.env ctx) cty in
  Global.add const cty (`Axiom, `Parametric);
  let (Wrap ptm) = Parse.Term.final (Parse.Term.parse (`String { content = tm; title = None })) in
  let rtm = process Emp ptm in
  let ctm = check (Potential (Constant (const, D.zero), Ctx.apps ctx, Ctx.lam ctx)) ctx rtm ety in
  Global.set const (`Defined ctm, `Parametric);
  (trie, ctm)

let install_isfibrant trie =
  let trie, ctm =
    def trie "isFibrant" "Type → Type"
      "A ↦ codata [
| x .trr.e : A.0 → A.1
| x .liftr.e : (x₀ : A.0) → A.2 x₀ (x.2 .trr x₀)
| x .trl.e : A.1 → A.0
| x .liftl.e : (x₁ : A.1) → A.2 (x.2 .trl x₁) x₁
| x .id.e : (x₀ : A.0) (x₁ : A.1) → isFibrant (A.2 x₀ x₁) ]"
  in
  (match ctm with
  | Lam (x, Canonical (Codata { eta = Noeta; dim; fields; _ })) -> (
      match (D.compare_zero (Variables.dim_variables x), D.compare_zero dim) with
      | Zero, Zero ->
          Fibrancy.fields :=
            (* The recursive "id" field is not exposed to the user; they access it simply by instantiating higher-dimensional types. *)
            Some
              (Bwd.filter
                 (fun (Term.CodatafieldAbwd.Entry (f, _)) ->
                   match Field.equal f Fibrancy.fid with
                   | Eq -> false
                   | Neq -> true)
                 fields)
      | _ -> fatal (Anomaly "isFibrant abstraction has wrong dimension"))
  | _ -> fatal (Anomaly "isFibrant has wrong shape"));
  trie

let install_bisim trie =
  let trie, _ =
    def trie "isBisim" "(A : Type) (B : Type) (R : A → B → Type) → Type"
      "A B R ↦ codata [
| x .trr : A → B
| x .liftr : (a : A) → R a (x .trr a)
| x .trl : B → A
| x .liftl : (b : B) → R (x .trl b) b
| x .id.e
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1)
    (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a2 b2 r0 r1) ]"
  in
  trie

let install_glue zero one trie =
  let ctx = Ctx.empty in
  let glue = Constant.make Compunit.basic in
  Scope.run ~init_visible:trie @@ fun () ->
  let (Wrap pty) =
    Parse.Term.final
      (Parse.Term.parse
         (`String
            {
              content =
                "(A : Type) (B : Type) (R : A → B → Type) (Rb : isBisim A B R) → Id Type A B";
              title = None;
            })) in
  let rty = process Emp pty in
  let cty = check (Kinetic `Nolet) ctx rty (universe D.zero) in
  Global.add glue cty (`Axiom, `Parametric);
  let trie = Scope.Mod.union_singleton ~prefix:Emp trie ([ "glue" ], ((`Constant glue, None), ())) in
  (* We construct this term by hand rather than by parsing and checking, to bypass the block on Gel-types under HOTT. *)
  let open Term in
  let aname = singleton_variables D.zero (Some "A") in
  let bname = singleton_variables D.zero (Some "B") in
  let rname = singleton_variables D.zero (Some "R") in
  let rbname = singleton_variables D.zero (Some "Rb") in
  let rvar = Var (Index (Later (Later Now), id_sface D.zero)) in
  let xvar = Var (Index (Now, zero)) in
  let yvar = Var (Index (Now, one)) in
  let entry =
    CodatafieldAbwd.Entry (Field.intern "unglue" D.zero, Lower (app (app rvar xvar) yvar)) in
  let gtm =
    app
      (app
         (app
            (app (Const glue) (Var (Index (Later (Later (Later Now)), id_sface D.zero))))
            (Var (Index (Later (Later Now), id_sface D.zero))))
         (Var (Index (Later Now, id_sface D.zero))))
      (Var (Index (Now, id_sface D.zero))) in
  let ctxlen =
    Plusmap.OfDom.Word (Plusmap.OfDom.Suc (Suc (Suc (Suc (Zero, D.zero), D.zero), D.zero), D.zero))
  in
  let (Fibrancy fibrancy) = Fibrancy.Codata.empty Hott.dim Hott.dim ctxlen Eta gtm in
  (* TODO: Add a field *)
  let ctm =
    Lam
      ( aname,
        Lam
          ( bname,
            Lam
              ( rname,
                Lam
                  ( rbname,
                    Canonical
                      (Codata
                         {
                           eta = Eta;
                           opacity = `Transparent `Unlabeled;
                           dim = Hott.dim;
                           termctx = None;
                           fields = Snoc (Emp, entry);
                           fibrancy;
                         }) ) ) ) ) in
  Global.set glue (`Defined ctm, `Parametric);
  trie

let install trie =
  match Hott.faces () with
  | None -> trie
  | Some (zero, one, _two) ->
      let _ = trie |> install_isfibrant in
      (* We don't expose isFibrant to the user *)
      trie |> install_bisim |> install_glue zero one
