open Dim
open Core
open Value
open Norm
open Check
open Notation
open Postprocess

let install trie =
  match Hott.faces () with
  | None -> trie
  | Some (zero, one, _two) ->
      (* isBisim *)
      let ctx = Ctx.empty in
      let (Wrap pty) =
        Parse.Term.final
          (Parse.Term.parse
             (`String { content = "(A : Type) (B : Type) (R : A → B → Type) → Type"; title = None }))
      in
      let rty = process Emp pty in
      let cty = check (Kinetic `Nolet) ctx rty (universe D.zero) in
      let ety = eval_term (Ctx.env ctx) cty in
      Global.add Fibrancy.bisim cty (`Axiom, `Parametric);
      let trie =
        Scope.Mod.union_singleton ~prefix:Emp trie
          ([ "isBisim" ], ((`Constant Fibrancy.bisim, None), ())) in
      Scope.run ~init_visible:trie @@ fun () ->
      let (Wrap ptm) =
        Parse.Term.final
          (Parse.Term.parse
             (`String
                {
                  content =
                    "A B R ↦ codata [
| x .trr : A → B
| x .liftr : (a : A) → R a (x .trr a)
| x .trl : B → A
| x .liftl : (b : B) → R (x .trl b) b
| x .id.e
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1)
    (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a0 a1 a2 b0 b1 b2 r0 r1) ]";
                  title = None;
                })) in
      let rtm = process Emp ptm in
      let ctm =
        check (Potential (Constant (Fibrancy.bisim, D.zero), Ctx.apps ctx, Ctx.lam ctx)) ctx rtm ety
      in
      Global.set Fibrancy.bisim (`Defined ctm, `Parametric);
      (* Glue *)
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
      Global.add Fibrancy.glue cty (`Axiom, `Parametric);
      let trie =
        Scope.Mod.union_singleton ~prefix:Emp trie
          ([ "glue" ], ((`Constant Fibrancy.glue, None), ())) in
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
                (app (Const Fibrancy.glue)
                   (Var (Index (Later (Later (Later Now)), id_sface D.zero))))
                (Var (Index (Later (Later Now), id_sface D.zero))))
             (Var (Index (Later Now, id_sface D.zero))))
          (Var (Index (Now, id_sface D.zero))) in
      let ctxlen =
        Plusmap.OfDom.Word
          (Plusmap.OfDom.Suc (Suc (Suc (Suc (Zero, D.zero), D.zero), D.zero), D.zero)) in
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
      Global.set Fibrancy.glue (`Defined ctm, `Parametric);
      (* Done! *)
      trie
