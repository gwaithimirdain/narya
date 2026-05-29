open Bwd
open Util
open Dim
open Modal
open Core
open Tctx
open Origin
open Value
open Variables
open Reporter

(* Here we bootstrap the HOTT fibrancy data using definitions that are parsed and checked.  The Narya code for this is stored in the following three source files, dropped here with ppx_blob. *)

let visible = [%blob "visible.ny"]
let isfibrant = [%blob "isfibrant.ny"]
let fibrancy = [%blob "fibrancy.ny"]

(* First we define some stripped-down versions of the batch file loading functions. *)

let rec batch p src =
  match Parser.Command.Parse.final p with
  | Eof -> ()
  | Bof _ ->
      let p, src = Parser.Command.Parse.restart_parse p src in
      batch p src
  | cmd ->
      let _ =
        Parser.Command.execute
          ~action_taken:(fun _ -> ())
          ~get_file:(fun _ -> fatal (Anomaly "can't load files during bootstrapping"))
          cmd in
      let p, src = Parser.Command.Parse.restart_parse p src in
      batch p src

let bootstrap title content =
  let title = Some title in
  let p, src = Parser.Command.Parse.start_parse (`String { title; content } : Asai.Range.source) in
  batch p src

(* For frobnicating things, we need to look up the defined terms that result from the bootstrapping. *)
let get name =
  match Parser.Scope.lookup name with
  | Some const -> const
  | None -> fatal (Anomaly (String.concat "." name ^ " not in scope"))

(* MODALTODO: We need to do all of this separately for each mode. *)

let () =
  (* MODALTODO: Deal with other modalities *)
  Modal.Trivial.install ();

  (* Wrap everything in the standard effect handlers *)
  Top.hott := false;
  Top.run_top ~install_hott:(fun () -> ()) ~interactive:false @@ fun () ->
  (* *)

  (* Load the visible bootstrap file, which defines isBisim and glue. *)
  Check.gel_ok := true;
  bootstrap "visible bootstrap" visible;
  Check.gel_ok := false;
  let glue = get [ "glue" ] in

  (* Mark glue as being glue. *)
  (match Global.find glue with
  | Definition
      {
        tm = `Defined (Lam (a, am, Lam (b, bm, Lam (r, rm, Lam (re, rem, Canonical (Codata c))))));
        mode;
        _;
      } -> (
      match
        ( D.compare_zero (dim_variables a),
          D.compare_zero (dim_variables b),
          D.compare_zero (dim_variables r),
          D.compare_zero (dim_variables re),
          Modality.compare_id am,
          Modality.compare_id bm,
          Modality.compare_id rm,
          Modality.compare_id rem,
          D.compare c.dim Hott.dim,
          c.eta )
      with
      | Zero, Zero, Zero, Zero, Eq, Eq, Eq, Eq, Eq, Eta ->
          let glue_def =
            Term.Lam
              ( a,
                am,
                Lam
                  ( b,
                    bm,
                    Lam (r, rm, Lam (re, rem, Canonical (Codata { c with is_glue = Some Glue }))) )
              ) in
          Global.set glue mode glue_def
      | _ -> fatal (Anomaly "glue has wrong dimension or modality"))
  | _ -> fatal (Anomaly "glue undefined"));

  (* Load the hidden isfibrant bootstrap file *)
  let isfibrant_file = File.make (`Other "isfibrant bootstrap") in
  ( Origin.with_file ~holes_allowed:false isfibrant_file @@ fun () ->
    bootstrap "isfibrant bootstrap" isfibrant;

    (* Use this to compute the types of fibrancy fields. *)
    let isfibrant = get [ "isFibrant" ] in
    match Global.find isfibrant with
    | Definition
        {
          tm = `Defined (Lam (x, modality, Canonical (Codata { eta = Noeta; dim; fields; _ })));
          mode;
          _;
        } -> (
        match
          (D.compare_zero (dim_variables x), D.compare_zero dim, Modality.compare_id modality)
        with
        | Zero, Zero, Eq ->
            Fibrancy.fields :=
              Fibrancy.FieldsMap.add mode
                (* The recursive "id" field is not exposed to the user; they access it simply by instantiating higher-dimensional types. *)
                (Bwd.filter
                   (fun (Term.CodatafieldAbwd.Entry (f, _)) ->
                     match Field.equal f Fibrancy.fid with
                     | Eq -> false
                     | Neq -> true)
                   fields)
                !Fibrancy.fields
        | _ -> fatal (Anomaly "isFibrant has wrong dimension or modality"))
    | _ -> fatal (Anomaly "isFibrant has wrong shape") );

  (* Load the hidden bootstrap file.  This requires that types already *have* fibrancy fields, so it has to be a separate file from hott-isfibrant. *)
  let fibrancy_file = File.make (`Other "fibrancy bootstrap") in
  ( Origin.with_file ~holes_allowed:false fibrancy_file @@ fun () ->
    bootstrap "fibrancy bootstrap" fibrancy;

    let eq_trr = get [ "eq"; "trr" ] in
    let eq_trr2 = get [ "eq"; "trr2" ] in
    let id_rtr = get [ "Id_rtr" ] in
    let fib_rtr = get [ "fib_rtr" ] in
    let id_pi_rtr = get [ "id_pi_rtr" ] in
    let glue_rtr = get [ "glue_rtr" ] in
    let fib_pi = get [ "fib_pi" ] in
    let fib_glue = get [ "fib_glue" ] in

    (* We remove the eq.trr's from the definition of fib_rtr, and the eq.trr2's from id_rtr, since they are always unnecessary computationally.  This doesn't seem to materially affect performance, but it's cleaner. *)
    (match Global.find fib_rtr with
    | Definition
        (type mode)
        ({
           tm =
             `Defined
               (Lam (aa, aam, Lam (bb, bbm, Lam (e, em, Struct ({ fields; eta = Noeta; _ } as s)))));
           mode;
           _;
         } :
          mode Global.definition_args) ->
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
                                    (type a)
                                    (( p,
                                       Lam
                                         (type k modality dom)
                                         (( b,
                                            bm,
                                            Realize
                                              (App
                                                 ( App
                                                     (App (App (App (App (Const c, _), _), _), _), _),
                                                   Modal (modality, plus, tm) )) ) :
                                           k variables * (dom, modality, mode) Modality.t * _) ) :
                                      _ * (mode, a, potential) Term.term)
                                  when c = eq_trr -> (
                                    match (Modality.compare_id modality, plus) with
                                    | Eq, Plus_lock (Zero _, Zero) ->
                                        Term.PlusFam.PlusFam
                                          ( p,
                                            Lam
                                              ( b,
                                                bm,
                                                Realize
                                                  (CubeOf.find_top tm
                                                    : ( mode,
                                                        (a, (modality, k) dim_entry) Tbwd.snoc,
                                                        kinetic )
                                                      Term.term) ) )
                                    | _ -> fatal (Anomaly "wrong modality in fib_rtr"))
                                | y -> y)
                              x);
                      }
                      [ tms ] in
                  Term.StructfieldAbwd.Entry (f, Higher tms)
              | s -> s)
            fields in
        Global.set fib_rtr mode
          (Lam (aa, aam, Lam (bb, bbm, Lam (e, em, Struct { s with fields }))))
    | _ -> ());
    (match Global.find id_rtr with
    | Definition
        (type mode)
        ({
           tm =
             `Defined
               (Lam
                  ( a0,
                    a0m,
                    Lam
                      ( a1,
                        a1m,
                        Lam
                          ( a2,
                            a2m,
                            Lam
                              ( b0,
                                b0m,
                                Lam
                                  ( b1,
                                    b1m,
                                    Lam
                                      ( b2,
                                        b2m,
                                        Lam
                                          ( e0,
                                            e0m,
                                            Lam
                                              ( e1,
                                                e1m,
                                                Lam (e2, e2m, Lam (x0, x0m, Lam (x1, x1m, Struct s)))
                                              ) ) ) ) ) ) ) ));
           mode;
           _;
         } :
          mode Global.definition_args) ->
        let field_mapper : type mode n a s et.
            (mode * (n * a * s * et)) Term.StructfieldAbwd.entry ->
            (mode * (n * a * s * et)) Term.StructfieldAbwd.entry = function
          | Term.StructfieldAbwd.Entry
              ( fld,
                Lower
                  ( Lam
                      (type k dom' modality')
                      (( b,
                         bm,
                         Realize
                           (App
                              (type dom modality n)
                              (( App
                                   ( App
                                       ( App
                                           ( App
                                               ( App (App (App (App (App (Const c, _), _), _), _), _),
                                                 _ ),
                                             _ ),
                                         _ ),
                                     _ ),
                                 Modal (modality, plus, tm) ) :
                                _
                                * ( n,
                                    dom,
                                    modality,
                                    mode,
                                    (a, (modality', k) dim_entry) Tbwd.snoc,
                                    kinetic )
                                  Term.modal_term_cube)) ) :
                        k variables * (dom', modality', mode) Modality.t * _),
                    l ) )
            when c = eq_trr2 -> (
              match (Modality.compare_id modality, plus) with
              | Eq, Plus_lock (Zero _, Zero) ->
                  Term.StructfieldAbwd.Entry
                    ( fld,
                      Lower
                        ( Lam
                            ( b,
                              bm,
                              Realize
                                (CubeOf.find_top tm
                                  : ( mode,
                                      (a, (modality', k) dim_entry) Tbwd.snoc,
                                      kinetic )
                                    Term.term) ),
                          l ) )
              | _ -> fatal (Anomaly "wrong modality in rtr"))
          | y -> y in
        let fields = Bwd.map field_mapper s.fields in
        Global.set id_rtr mode
          (Lam
             ( a0,
               a0m,
               Lam
                 ( a1,
                   a1m,
                   Lam
                     ( a2,
                       a2m,
                       Lam
                         ( b0,
                           b0m,
                           Lam
                             ( b1,
                               b1m,
                               Lam
                                 ( b2,
                                   b2m,
                                   Lam
                                     ( e0,
                                       e0m,
                                       Lam
                                         ( e1,
                                           e1m,
                                           Lam
                                             ( e2,
                                               e2m,
                                               Lam (x0, x0m, Lam (x1, x1m, Struct { s with fields }))
                                             ) ) ) ) ) ) ) ) ))
    | _ -> ());

    (* We adjust the case tree boundary for id_pi_rtr to avoid exposing that constant to the user when a higher fibrancy field is applied only to a function but not a further argument. *)
    (match Global.find id_pi_rtr with
    | Definition
        {
          tm =
            `Defined
              (Lam
                 ( a0,
                   a0m,
                   Lam
                     ( a1,
                       a1m,
                       Lam
                         ( a2,
                           a2m,
                           Lam
                             ( b0,
                               b0m,
                               Lam (b1, b1m, Lam (b2, b2m, Lam (f0, f0m, Lam (f1, f1m, Struct s))))
                             ) ) ) ));
          mode;
          _;
        } ->
        let fields =
          Bwd.map
            Term.StructfieldAbwd.(
              function
              | Entry (fld, Lower (Lam (f, fm, Lam (a, am, Realize tm)), l)) ->
                  Entry (fld, Lower (Lam (f, fm, Realize (Lam (a, am, tm))), l))
              | Entry
                  ( fld,
                    Lower (Lam (f, fm, Lam (a0, a0m, Lam (a1, a1m, Lam (a2, a2m, Realize tm)))), l)
                  ) ->
                  Entry
                    ( fld,
                      Lower
                        (Lam (f, fm, Realize (Lam (a0, a0m, Lam (a1, a1m, Lam (a2, a2m, tm))))), l)
                    )
              | s -> s)
            s.fields in
        Global.set id_pi_rtr mode
          (Lam
             ( a0,
               a0m,
               Lam
                 ( a1,
                   a1m,
                   Lam
                     ( a2,
                       a2m,
                       Lam
                         ( b0,
                           b0m,
                           Lam
                             ( b1,
                               b1m,
                               Lam (b2, b2m, Lam (f0, f0m, Lam (f1, f1m, Struct { s with fields })))
                             ) ) ) ) ))
    | _ -> fatal (Anomaly "id_pi_rtr undefined"));

    (* As with id_pi_rtr, so with glue_rtr *)
    (match Global.find glue_rtr with
    | Definition
        {
          tm =
            `Defined
              (Lam
                 ( aa,
                   aam,
                   Lam (bb, bbm, Lam (rr, rrm, Lam (re, rem, Lam (a, am, Lam (b, bm, Struct s)))))
                 ));
          mode;
          _;
        } ->
        let fields =
          Bwd.map
            Term.StructfieldAbwd.(
              function
              | Entry
                  ( fld,
                    Lower (Lam (r, rm, Struct { dim; fields; eta = Eta; energy = Potential }), l) )
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
                      Lower
                        ( Lam (r, rm, Realize (Struct { dim; fields; eta = Eta; energy = Kinetic })),
                          l ) )
              | x -> x)
            s.fields in
        Global.set glue_rtr mode
          (Lam
             ( aa,
               aam,
               Lam
                 ( bb,
                   bbm,
                   Lam (rr, rrm, Lam (re, rem, Lam (a, am, Lam (b, bm, Struct { s with fields }))))
                 ) ))
    | _ -> fatal (Anomaly "glue_rtr_rtr undefined"));

    (* Now we pull out the fields from the definition of fib_pi to insert them in Fibrancy.pi. *)
    (match Global.find fib_pi with
    | Definition
        {
          tm =
            `Defined
              (Lam (a, am, Lam (b, bm, Struct { dim; fields; eta = Noeta; energy = Potential })));
          _;
        } -> (
        match
          ( D.compare_zero (dim_variables a),
            D.compare_zero (dim_variables b),
            D.compare_zero dim,
            (* The type of fib_pi is "(A : Type) (B : A → Type) → isFibrant ((x : A) → B x)", which in the modal case becomes "(A :: Type) (B : (x :: A) → Type) → isFibrant ((x :: A) → B x)".  So the modality of A can be nontrivial, but that of B should be trivial. *)
            Modality.compare_id bm )
        with
        | Zero, Zero, Zero, Eq ->
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
                                    | Term.PlusFam.PlusFam (p, Lam (f, fm, Lam (a, am, Realize tm)))
                                      ->
                                        Term.PlusFam.PlusFam
                                          (p, Lam (f, fm, Realize (Lam (a, am, tm))))
                                    | y -> y)
                                  x);
                          }
                          [ tms ] in
                      Term.StructfieldAbwd.Entry (f, Higher tms)
                  | s -> s)
                fields in
            Fibrancy.pi := Fibrancy.PiValuesMap.add am fields !Fibrancy.pi
        | _ -> fatal (Anomaly "fib_pi has wrong dimension or mode"))
    | _ -> fatal (Anomaly "fib_pi has wrong shape"));

    (* And similarly for Fibrancy.glue. *)
    match Global.find fib_glue with
    | Definition
        {
          tm =
            `Defined
              (Lam
                 ( a,
                   am,
                   Lam
                     ( b,
                       bm,
                       Lam
                         ( r,
                           rm,
                           Lam (re, rem, Struct { dim; fields; eta = Noeta; energy = Potential }) )
                     ) ));
          mode;
          _;
        } -> (
        match
          ( D.compare_zero (dim_variables a),
            D.compare_zero (dim_variables b),
            D.compare_zero (dim_variables r),
            D.compare_zero (dim_variables re),
            Modality.compare_id am,
            Modality.compare_id bm,
            Modality.compare_id rm,
            Modality.compare_id rem,
            D.compare dim Hott.dim )
        with
        | Zero, Zero, Zero, Zero, Eq, Eq, Eq, Eq, Eq ->
            Fibrancy.glue := Fibrancy.GlueValuesMap.add mode fields !Fibrancy.glue
        | _ -> fatal (Anomaly "fib_glue has wrong dimension"))
    | _ -> fatal (Anomaly "fib_glue has wrong shape") );

  let ofile =
    if Array.length Sys.argv <> 2 then (
      print_endline "usage: bootstrap outfile";
      exit 1)
    else Sys.argv.(1) in
  Out_channel.with_open_bin ofile @@ fun chan -> Io.marshal chan isfibrant_file fibrancy_file
