open Bwd
open Dim
open Core
open Value
open Norm
open Check
open Variables
open Notation
open Postprocess
open Reporter

let def_term name ty tm trie =
  let ctx = Ctx.empty in
  let const = Constant.make Compunit.basic in
  let name = String.split_on_char '.' name in
  let trie = Scope.Mod.union_singleton ~prefix:Emp trie (name, ((`Constant const, None), ())) in
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
  (const, trie, ctm)

let def name ty tm trie =
  let _, trie, _ = def_term name ty tm trie in
  trie

let install_isfibrant trie =
  let _, trie, ctm =
    def_term "isFibrant" "Type → Type"
      "A ↦ codata [
| x .trr.e : A.0 → A.1
| x .liftr.e : (x₀ : A.0) → A.2 x₀ (x.2 .trr x₀)
| x .trl.e : A.1 → A.0
| x .liftl.e : (x₁ : A.1) → A.2 (x.2 .trl x₁) x₁
| x .id.e : (x₀ : A.0) (x₁ : A.1) → isFibrant (A.2 x₀ x₁) ]"
      trie in
  (match ctm with
  | Lam (x, Canonical (Codata { eta = Noeta; dim; fields; _ })) -> (
      match (D.compare_zero (dim_variables x), D.compare_zero dim) with
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
      | _ -> fatal (Anomaly "isFibrant has wrong dimension"))
  | _ -> fatal (Anomaly "isFibrant has wrong shape"));
  trie

(* To compute the fibrancy fields of a pi-type, we basically copy a minimal part of the code from the proof in binary parametricity that pi-types are fibrant, with a few changes.  First we typecheck a proof that fibrancy is preserved under retraction. *)

let install_rtr trie =
  let eq_trr, trie, _ =
    trie
    (* We include the Martin-Lof equality so that everything will typecheck, although in practice it will turn out to always be rfl and thus reduce away. *)
    |> def "eq" "(A : Type) (a : A) → A → Type" "A a ↦ data [ rfl. : eq A a a ]"
    |> def_term "eq.trr" "(A : Type) (P : A → Type) (a0 a1 : A) (a2 : eq A a0 a1) (p : P a0) → P a1"
         "A P a0 a1 a2 p ↦ match a2 [ rfl. ↦ p ]" in
  let eq_trr2, trie, _ =
    trie
    |> def_term "eq.trr2"
         "(A : Type) (B : Type) (P : A → B → Type) (a0 a1 : A)
  (a2 : eq A a0 a1) (b0 b1 : B) (b2 : eq B b0 b1) (p : P a0 b0)
  → P a1 b1"
         "A B P a0 a1 a2 b0 b1 b2 p ↦ match a2, b2 [ rfl., rfl. ↦ p ]" in
  let id_rtr, trie, _ =
    trie
    (* We don't need a full equivalence, only a retraction. *)
    |> def "rtr" "(A B : Type) → Type"
         "A B ↦ sig (
  to : A → B,
  fro : B → A,
  to_fro : (b : B) → eq B (to (fro b)) b )"
    |> def "Id_eq"
         "(A0 A1 : Type) (A2 : Id Type A0 A1) (a00 : A0) (a01 : A1)
  (a02 : A2 a00 a01) (a10 : A0) (a11 : A1) (a12 : A2 a10 a11)
  (a20 : eq A0 a00 a10) (a21 : eq A1 a01 a11)
  (a22 : Id eq A2 a02 a12 a20 a21)
  → eq (A2 a10 a11)
      (eq.trr2 A0 A1 (x y ↦ A2 x y) a00 a10 a20 a01 a11 a21 a02) a12"
         "A0 A1 A2 a00 a01 a02 a10 a11 a12 a20 a21 a22 ↦ match a22 [ rfl. ⤇ rfl. ]"
    |> def_term "Id_rtr"
         "(A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : Type)
  (B1 : Type) (B2 : Id Type B0 B1) (e0 : rtr A0 B0) (e1 : rtr A1 B1)
  (e2 : Id rtr A2 B2 e0 e1) (b0 : B0) (b1 : B1)
  → rtr (A2 (e0 .fro b0) (e1 .fro b1)) (B2 b0 b1)"
         "A0 A1 A2 B0 B1 B2 e0 e1 e2 b0 b1 ↦
 (to ≔ a2 ↦
    eq.trr2 B0 B1 (b0 b1 ↦ B2 b0 b1) (e0 .to (e0 .fro b0)) b0
      (e0 .to_fro b0) (e1 .to (e1 .fro b1)) b1 (e1 .to_fro b1) (e2 .to a2),
  fro ≔ b2 ↦ e2 .fro b2,
  to_fro ≔ b2 ↦
    Id_eq B0 B1 B2 (e0 .to (e0 .fro b0)) (e1 .to (e1 .fro b1))
      (e2 .to (e2 .fro b2)) b0 b1 b2 (e0 .to_fro b0) (e1 .to_fro b1)
      (e2 .to_fro b2))"
  in
  (* Here we can cheat a little: since we're already in HOTT, we don't need to assume an explicit witness of fibrancy for the given type A, we can just use its intrinsic one. *)
  let fib_rtr, trie, _ =
    trie
    |> def_term "fib_rtr" "(A B : Type) (e : rtr A B) → isFibrant B"
         "A B e ↦ [
| .trr.e ↦ b0 ↦ e.1 .to (A.2 .trr (e.0 .fro b0))
| .trl.e ↦ b1 ↦ e.0 .to (A.2 .trl (e.1 .fro b1))
| .liftr.e ↦ b0 ↦
    eq.trr B.0 (b ↦ B.2 b (e.1 .to (A.2 .trr (e.0 .fro b0))))
      (e.0 .to (e.0 .fro b0)) b0 (e.0 .to_fro b0)
      (e.2 .to (A.2 .liftr (e.0 .fro b0)))
| .liftl.e ↦ b1 ↦
    eq.trr B.1 (b ↦ B.2 (e.0 .to (A.2 .trl (e.1 .fro b1))) b)
      (e.1 .to (e.1 .fro b1)) b1 (e.1 .to_fro b1)
      (e.2 .to (A.2 .liftl (e.1 .fro b1)))
| .id.e ↦ b0 b1 ↦
    fib_rtr (A.2 (e.0 .fro b0) (e.1 .fro b1)) (B.2 b0 b1)
      (Id_rtr A.0 A.1 A.2 B.0 B.1 B.2 e.0 e.1 e.2 b0 b1)]"
  in
  let trie =
    trie
    |> def "sym_rtr"
         "(A00 A01 : Type) (A02 : Id Type A00 A01) (A10 A11 : Type)
    (A12 : Id Type A10 A11) (A20 : Id Type A00 A10) (A21 : Id Type A01 A11)
    (A22 : Id (Id Type) A02 A12 A20 A21) (a00 : A00) (a01 : A01)
    (a02 : A02 a00 a01) (a10 : A10) (a11 : A11) (a12 : A12 a10 a11)
    (a20 : A20 a00 a10) (a21 : A21 a01 a11)
    → rtr (A22 a02 a12 a20 a21) (sym A22 a20 a21 a02 a12)"
         "A00 A01 A02 A10 A11 A12 A20 A21 A22 a00 a01 a02 a10 a11 a12 a20 a21 ↦ (
  to ≔ a22 ↦ sym a22,
  fro ≔ a22 ↦ sym a22,
  to_fro ≔ _ ↦ rfl.)"
    |> def "isbisim_rtr"
         "(A B : Type) (R S : A → B → Type)
    (e : (a : A) (b : B) → rtr (R a b) (S a b)) (Re : isBisim A B R)
    → isBisim A B S"
         "A B R S e Re ↦ [
| .trr ↦ a ↦ Re .trr a
| .liftr ↦ a ↦ e a (Re .trr a) .to (Re .liftr a)
| .trl ↦ b ↦ Re .trl b
| .liftl ↦ b ↦ e (Re .trl b) b .to (Re .liftl b)
| .id.e ↦ a0 b0 s0 a1 b1 s1 ↦
    isbisim_rtr (A.2 a0 a1) (B.2 b0 b1)
      (a2 b2 ↦ R.2 a2 b2 (e.0 a0 b0 .fro s0) (e.1 a1 b1 .fro s1))
      (a2 b2 ↦ S.2 a2 b2 s0 s1)
      (a2 b2 ↦
       Id_rtr (R.0 a0 b0) (R.1 a1 b1) (R.2 a2 b2) (S.0 a0 b0) (S.1 a1 b1)
         (S.2 a2 b2) (e.0 a0 b0) (e.1 a1 b1) (e.2 a2 b2) s0 s1)
      (Re.2 .id a0 b0 (e.0 a0 b0 .fro s0) a1 b1 (e.1 a1 b1 .fro s1))]"
    |> def "fib_any" "(A : Type) → isFibrant A"
         "A ↦ [
| .trr.e ↦ A.2 .trr
| .liftr.e ↦ A.2 .liftr
| .trl.e ↦ A.2 .trl
| .liftl.e ↦ A.2 .liftl
| .id.e ↦ x₀ x₁ ↦ fib_any (A.2 x₀ x₁)]"
  in
  (* Now we remove the eq.trr's from fib_rtr, and the eq.trr2's from id_rtr, since they are always unnecessary computationally.  This doesn't seem to materially affect performance, but it's cleaner. *)
  (match Global.find fib_rtr with
  | _, (`Defined (Lam (aa, Lam (bb, Lam (e, Struct ({ fields; eta = Noeta; _ } as s))))), param) ->
      let fields =
        Bwd.map
          (function
            | Term.StructfieldAbwd.Entry (f, Higher tms) ->
                let tms =
                  Term.PlusPbijmap.mmap
                    {
                      map =
                        (fun _ [ x ] ->
                          Option.map
                            (function
                              | Term.PlusFam.PlusFam
                                  ( p,
                                    Lam
                                      ( b,
                                        Realize
                                          (App
                                             ( App (App (App (App (App (Const c, _), _), _), _), _),
                                               tm )) ) )
                                when c = eq_trr ->
                                  Term.PlusFam.PlusFam (p, Lam (b, Realize (CubeOf.find_top tm)))
                              | y -> y)
                            x);
                    }
                    [ tms ] in
                Term.StructfieldAbwd.Entry (f, Higher tms)
            | s -> s)
          fields in
      Global.set fib_rtr (`Defined (Lam (aa, Lam (bb, Lam (e, Struct { s with fields })))), param)
  | _ -> ());
  (match Global.find id_rtr with
  | ( _,
      ( `Defined
          (Lam
             ( a0,
               Lam
                 ( a1,
                   Lam
                     ( a2,
                       Lam
                         ( b0,
                           Lam
                             ( b1,
                               Lam (b2, Lam (e0, Lam (e1, Lam (e2, Lam (x0, Lam (x1, Struct s))))))
                             ) ) ) ) )),
        param ) ) ->
      let fields =
        Bwd.map
          (function
            | Term.StructfieldAbwd.Entry
                ( fld,
                  Lower
                    ( Lam
                        ( b,
                          Realize
                            (App
                               ( App
                                   ( App
                                       ( App
                                           ( App
                                               ( App (App (App (App (App (Const c, _), _), _), _), _),
                                                 _ ),
                                             _ ),
                                         _ ),
                                     _ ),
                                 tm )) ),
                      l ) )
              when c = eq_trr2 ->
                Term.StructfieldAbwd.Entry (fld, Lower (Lam (b, Realize (CubeOf.find_top tm)), l))
            | y -> y)
          s.fields in
      Global.set id_rtr
        ( `Defined
            (Lam
               ( a0,
                 Lam
                   ( a1,
                     Lam
                       ( a2,
                         Lam
                           ( b0,
                             Lam
                               ( b1,
                                 Lam
                                   ( b2,
                                     Lam
                                       ( e0,
                                         Lam
                                           ( e1,
                                             Lam (e2, Lam (x0, Lam (x1, Struct { s with fields })))
                                           ) ) ) ) ) ) ) )),
          param )
  | _ -> ());
  trie

(* Now we do pi-types based on that. *)
let install_fib_pi trie =
  let id_pi_rtr, trie, _ =
    trie
    |> def_term "id_pi_rtr"
         "(A0 : Type) (A1 : Type) (A2 : Id Type A0 A1) (B0 : A0 → Type)
  (B1 : A1 → Type)
  (B2 : Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A2
          {_ ↦ Type} {_ ↦ Type} (_ ⤇ refl Type) B0 B1)
  (f0 : (a0 : A0) → B0 a0) (f1 : (a1 : A1) → B1 a1)
  → rtr ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
      (Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A2 B2 f0
         f1)"
         "A0 A1 A2 B0 B1 B2 f0 f1 ↦
         (
  to ≔ f ↦ a ⤇ f a.0 a.1 a.2,
  fro ≔ g ↦ a0 a1 a2 ↦ g a2,
  to_fro ≔ _ ↦ rfl.)"
  in
  let _, trie, ctm =
    trie
    |> def_term "fib_pi" "(A : Type) (B : A → Type) → isFibrant ((x : A) → B x)"
         "A B ↦ [
| .trr.e ↦ f0 ↦ a1 ↦ B.2 (A.2 .liftl a1) .trr (f0 (A.2 .trl a1))
| .trl.e ↦ f1 ↦ a0 ↦ B.2 (A.2 .liftr a0) .trl (f1 (A.2 .trr a0))
| .liftr.e ↦ f0 ↦
      a ⤇
       refl B.2
           (sym (sym (refl A.2) a.2 (A.2 .liftl a.1) .liftl (refl a.1)))
           (refl f0 (A.2⁽ᵉ¹⁾ a.2 (A.2 .liftl a.1) .trl (refl a.1)))
           (refl (B.2 (A.2 .liftl a.1) .trr (f0 (A.2 .trl a.1))))
       .trl (B.2 (A.2 .liftl a.1) .liftr (f0 (A.2 .trl a.1)))
| .liftl.e ↦ f1 ↦
      a ⤇
       refl B.2
           (sym (sym (refl A.2) a.2 (A.2 .liftr a.0) .liftr (refl a.0)))
           (refl (B.2 (A.2 .liftr a.0) .trl (f1 (A.2 .trr a.0))))
           (refl f1 (A.2⁽ᵉ¹⁾ a.2 (A.2 .liftr a.0) .trr (refl a.0)))
       .trl (B.2 (A.2 .liftr a.0) .liftl (f1 (A.2 .trr a.0)))
| .id.e ↦ f0 f1 ↦
    fib_rtr
      ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
      (Id ((X Y ↦ (x : X) → Y x) : (X : Type) → (X → Type) → Type) A.2 B.2
         f0 f1) (id_pi_rtr A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)]"
  in
  (* Now we pull out the fields from the above definition of fib_pi to insert them in Fibrancy.pi. *)
  (match ctm with
  | Lam (a, Lam (b, Struct { dim; fields; eta = Noeta; energy = Potential })) -> (
      match
        (D.compare_zero (dim_variables a), D.compare_zero (dim_variables b), D.compare_zero dim)
      with
      | Zero, Zero, Zero ->
          (* We rearrange the end of the case trees for tr and lift so that after applying to a single function argument they compute to an abstraction.  This is actually not what we'd want in principle, but we do it for consistency with the higher-dimensional case where we don't seem to have another option. *)
          let fields =
            Bwd.map
              (function
                | Term.StructfieldAbwd.Entry (f, Higher tms) ->
                    let tms =
                      Term.PlusPbijmap.mmap
                        {
                          map =
                            (fun _ [ x ] ->
                              Option.map
                                (function
                                  | Term.PlusFam.PlusFam (p, Lam (f, Lam (a, Realize tm))) ->
                                      Term.PlusFam.PlusFam (p, Lam (f, Realize (Lam (a, tm))))
                                  | y -> y)
                                x);
                        }
                        [ tms ] in
                    Term.StructfieldAbwd.Entry (f, Higher tms)
                | s -> s)
              fields in
          Fibrancy.pi := Some fields
      | _ -> fatal (Anomaly "fib_pi has wrong dimension"))
  | _ -> fatal (Anomaly "fib_pi has wrong shape"));
  (* For the higher-dimensional case, we have to adjust the case tree boundary for id_pi_rtr to avoid exposing that constant to the user when a higher fibrancy field is applied only to a function but not a further argument. *)
  (match Global.find id_pi_rtr with
  | ( _,
      ( `Defined
          (Lam (a0, Lam (a1, Lam (a2, Lam (b0, Lam (b1, Lam (b2, Lam (f0, Lam (f1, Struct s))))))))),
        param ) ) ->
      let fields =
        Bwd.map
          Term.StructfieldAbwd.(
            function
            | Entry (fld, Lower (Lam (f, Lam (a, Realize tm)), l)) ->
                Entry (fld, Lower (Lam (f, Realize (Lam (a, tm))), l))
            | Entry (fld, Lower (Lam (f, Lam (a0, Lam (a1, Lam (a2, Realize tm)))), l)) ->
                Entry (fld, Lower (Lam (f, Realize (Lam (a0, Lam (a1, Lam (a2, tm))))), l))
            | s -> s)
          s.fields in
      Global.set id_pi_rtr
        ( `Defined
            (Lam
               ( a0,
                 Lam
                   ( a1,
                     Lam
                       ( a2,
                         Lam (b0, Lam (b1, Lam (b2, Lam (f0, Lam (f1, Struct { s with fields })))))
                       ) ) )),
          param )
  | _ -> fatal (Anomaly "id_pi_rtr undefined"));
  trie

let install_bisim trie =
  def "isBisim" "(A : Type) (B : Type) (R : A → B → Type) → Type"
    "A B R ↦ codata [
| x .trr : A → B
| x .liftr : (a : A) → R a (x .trr a)
| x .trl : B → A
| x .liftl : (b : B) → R (x .trl b) b
| x .id.e
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1)
    (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a2 b2 r0 r1) ]"
    trie

let install_glue trie =
  let glue, trie, _ =
    trie
    |> def_term "glue" "(A : Type) (B : Type) (R : A → B → Type) (Rb : isBisim A B R) → Id Type A B"
         "A B R Rb ↦ sig x y ↦ ( unglue : R x y )" in
  (match Global.find glue with
  | _, (`Defined (Lam (a, Lam (b, Lam (r, Lam (re, Canonical (Codata c)))))), param) -> (
      match
        ( D.compare_zero (dim_variables a),
          D.compare_zero (dim_variables b),
          D.compare_zero (dim_variables r),
          D.compare_zero (dim_variables re),
          D.compare c.dim Hott.dim,
          c.eta )
      with
      | Zero, Zero, Zero, Zero, Eq, Eta ->
          Global.set glue
            ( `Defined
                (Lam
                   (a, Lam (b, Lam (r, Lam (re, Canonical (Codata { c with is_glue = Some Glue })))))),
              param )
      | _ -> fatal (Anomaly "glue has wrong dimension"))
  | _ -> fatal (Anomaly "glue undefined"));
  Check.gel_ok := false;
  trie

let install_fib_glue trie =
  let glue_rtr, trie, _ =
    trie
    |> def "pre_univalence"
         "(A : Type) (B : Type) (G : Id Type A B)
    (fibG : (a : A) (b : B) → isFibrant (G a b))
    (Ge : isBisim A B (x y ↦ G x y))
    → Id isFibrant G (fib_any A) (fib_any B)"
         "A B G fibG Ge ↦ [
| .trr.1 ↦ a ↦ Ge .trr a
| .trl.1 ↦ b ↦ Ge .trl b
| .liftr.1 ↦ a ↦ Ge .liftr a
| .liftl.1 ↦ b ↦ Ge .liftl b
| .id.1 ↦ a b ↦ fibG a b
| .trr.e ↦ {a0} {b0} r0 ↦ fibG.2 (A.2 .liftr a0) (B.2 .liftr b0) .trr r0
| .trl.e ↦ {a1} {b1} r1 ↦ fibG.2 (A.2 .liftl a1) (B.2 .liftl b1) .trl r1
| .liftr.e ↦ {a0} {b0} r0 ↦
    sym (fibG.2 (A.2 .liftr a0) (B.2 .liftr b0) .liftr r0)
| .liftl.e ↦ {a1} {b1} r1 ↦
    sym (fibG.2 (A.2 .liftl a1) (B.2 .liftl b1) .liftl r1)
| .id.e ↦ {a0} {b0} r0 {a1} {b1} r1 ↦
    pre_univalence (A.2 a0 a1) (B.2 b0 b1) (sym G.2 r0 r1)
      (a2 b2 ↦
       fib_rtr (G.2 a2 b2 r0 r1) (sym G.2 r0 r1 a2 b2)
         (sym_rtr A.0 A.1 A.2 B.0 B.1 B.2 G.0 G.1 G.2 a0 a1 a2 b0 b1 b2 r0
            r1))
      (isbisim_rtr (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ G.2 a2 b2 r0 r1)
         (a2 b2 ↦ sym G.2 r0 r1 a2 b2)
         (a2 b2 ↦
          sym_rtr A.0 A.1 A.2 B.0 B.1 B.2 G.0 G.1 G.2 a0 a1 a2 b0 b1 b2 r0
            r1) (Ge.2 .id a0 b0 r0 a1 b1 r1))]"
    |> def_term "glue_rtr"
         "(A B : Type) (R : A → B → Type) (Re : isBisim A B R) (a : A) (b : B)
    → rtr (R a b) (glue A B R Re a b)"
         "A B R Re a b ↦ (to ≔ r ↦ (r,), fro ≔ g ↦ g .0, to_fro ≔ _ ↦ rfl.)" in
  (* Finally we prove that glue-types are fibrant.  Like with fibrancy of pi, this is essentially a copy of the proof of univalence in hct-hott, modified to make sense in a fibrant world.  In addition, instead of calling directly to pre_univalence, we eta-expand the definition once, pasting in the definition of pre_univalence; this way we ensure that the resulting term is a struct and we can extract its fields to insert into the fibrancy fields of glue. *)
  let _, trie, ctm =
    trie
    |> def_term "fib_glue"
         "(A B : Type) (R : A → B → Type) (Re : isBisim A B R)
    → Id isFibrant (glue A B R Re) (fib_any A) (fib_any B)"
         "A B R Re ↦ [
| .trr.1 ↦ a ↦
    isbisim_rtr A B (x y ↦ R x y) (a b ↦ glue A B R Re a b)
        (glue_rtr A B R Re) Re
      .trr a
| .trl.1 ↦ b ↦
    isbisim_rtr A B (x y ↦ R x y) (a b ↦ glue A B R Re a b)
        (glue_rtr A B R Re) Re
      .trl b
| .liftr.1 ↦ a ↦
    isbisim_rtr A B (x y ↦ R x y) (a b ↦ glue A B R Re a b)
        (glue_rtr A B R Re) Re
      .liftr a
| .liftl.1 ↦ b ↦
    isbisim_rtr A B (x y ↦ R x y) (a b ↦ glue A B R Re a b)
        (glue_rtr A B R Re) Re
      .liftl b
| .id.1 ↦ a b ↦ fib_rtr (R a b) (glue A B R Re a b) (glue_rtr A B R Re a b)
| .trr.e ↦ {a0} {b0} r0 ↦
    refl fib_rtr (R.2 (A.2 .liftr a0) (B.2 .liftr b0))
        (refl glue A.2 B.2 R.2 Re.2 (A.2 .liftr a0) (B.2 .liftr b0))
        (refl glue_rtr A.2 B.2 R.2 Re.2 (A.2 .liftr a0) (B.2 .liftr b0))
      .trr r0
| .trl.e ↦ {a1} {b1} r1 ↦
    refl fib_rtr (R.2 (A.2 .liftl a1) (B.2 .liftl b1))
        (refl glue A.2 B.2 R.2 Re.2 (A.2 .liftl a1) (B.2 .liftl b1))
        (refl glue_rtr A.2 B.2 R.2 Re.2 (A.2 .liftl a1) (B.2 .liftl b1))
      .trl r1
| .liftr.e ↦ {a0} {b0} r0 ↦
    sym
      (refl fib_rtr (R.2 (A.2 .liftr a0) (B.2 .liftr b0))
           (refl glue A.2 B.2 R.2 Re.2 (A.2 .liftr a0) (B.2 .liftr b0))
           (refl glue_rtr A.2 B.2 R.2 Re.2 (A.2 .liftr a0) (B.2 .liftr b0))
       .liftr r0)
| .liftl.e ↦ {a1} {b1} r1 ↦
    sym
      (refl fib_rtr (R.2 (A.2 .liftl a1) (B.2 .liftl b1))
           (refl glue A.2 B.2 R.2 Re.2 (A.2 .liftl a1) (B.2 .liftl b1))
           (refl glue_rtr A.2 B.2 R.2 Re.2 (A.2 .liftl a1) (B.2 .liftl b1))
       .liftl r1)
| .id.e ↦ {a0} {b0} r0 {a1} {b1} r1 ↦
    pre_univalence (A.2 a0 a1) (B.2 b0 b1)
      (sym (refl glue A.2 B.2 R.2 Re.2) r0 r1)
      (a2 b2 ↦
       fib_rtr (refl glue A.2 B.2 R.2 Re.2 a2 b2 r0 r1)
         (sym (refl glue A.2 B.2 R.2 Re.2) r0 r1 a2 b2)
         (sym_rtr A.0 A.1 A.2 B.0 B.1 B.2 (glue A.0 B.0 R.0 Re.0)
            (glue A.1 B.1 R.1 Re.1) (refl glue A.2 B.2 R.2 Re.2) a0 a1 a2
            b0 b1 b2 r0 r1))
      (isbisim_rtr (A.2 a0 a1) (B.2 b0 b1)
         (a2 b2 ↦ (refl glue A.2 B.2 R.2 Re.2) a2 b2 r0 r1)
         (a2 b2 ↦ sym (refl glue A.2 B.2 R.2 Re.2) r0 r1 a2 b2)
         (a2 b2 ↦
          sym_rtr A.0 A.1 A.2 B.0 B.1 B.2 (glue A.0 B.0 R.0 Re.0)
            (glue A.1 B.1 R.1 Re.1) (refl glue A.2 B.2 R.2 Re.2) a0 a1 a2
            b0 b1 b2 r0 r1)
         (refl isbisim_rtr A.2 B.2 {R.0} {R.1} (x y ⤇ R.2 x.2 y.2)
              {a b ↦ glue A.0 B.0 R.0 Re.0 a b}
              {a b ↦ glue A.1 B.1 R.1 Re.1 a b}
              (a b ⤇ refl glue A.2 B.2 R.2 Re.2 a.2 b.2)
              (refl glue_rtr A.2 B.2 R.2 Re.2) Re.2
          .id a0 b0 r0 a1 b1 r1))]"
  in
  (match ctm with
  | Lam (a, Lam (b, Lam (r, Lam (re, Struct { dim; fields; eta = Noeta; energy = Potential }))))
    -> (
      match
        ( D.compare_zero (dim_variables a),
          D.compare_zero (dim_variables b),
          D.compare_zero (dim_variables r),
          D.compare_zero (dim_variables re),
          D.compare dim Hott.dim )
      with
      | Zero, Zero, Zero, Zero, Eq -> Fibrancy.glue := Some fields
      | _ -> fatal (Anomaly "fib_glue has wrong dimension"))
  | _ -> fatal (Anomaly "fib_glue has wrong shape"));
  (* As with id_pi_rtr, so with glue_rtr *)
  (match Global.find glue_rtr with
  | _, (`Defined (Lam (aa, Lam (bb, Lam (rr, Lam (re, Lam (a, Lam (b, Struct s))))))), param) ->
      let fields =
        Bwd.map
          Term.StructfieldAbwd.(
            function
            | Entry (fld, Lower (Lam (r, Struct { dim; fields; eta = Eta; energy = Potential }), l))
              ->
                let fields =
                  Bwd.map
                    Term.StructfieldAbwd.(
                      function
                      | Entry (stfld, Lower (Realize y, stl)) -> Entry (stfld, Lower (y, stl))
                      | _ -> fatal (Anomaly "glue_rtr has wrong shape"))
                    fields in
                Entry
                  ( fld,
                    Lower (Lam (r, Realize (Struct { dim; fields; eta = Eta; energy = Kinetic })), l)
                  )
            | x -> x)
          s.fields in
      Global.set glue_rtr
        ( `Defined
            (Lam (aa, Lam (bb, Lam (rr, Lam (re, Lam (a, Lam (b, Struct { s with fields }))))))),
          param )
  | _ -> fatal (Anomaly "glue_rtr_rtr undefined"));
  trie

let install trie =
  match Hott.faces () with
  | None -> trie
  | Some (_zero, _one, _two) ->
      let trie = trie |> install_bisim |> install_glue in
      (* We don't expose isFibrant to the user *)
      let _ = trie |> install_isfibrant |> install_rtr |> install_fib_pi |> install_fib_glue in
      trie
