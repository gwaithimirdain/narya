open Bwd
open Dim
module ParserCommand = Command
open Core
open Origin
open Value
open Variables
open Reporter

(* Here we bootstrap the HOTT fibrancy data using definitions that are parsed and checked.  They are stored in the following three files, dropped here with ppx_blob and then loaded like command-line exec strings.  Note that this means they are parsed and typechecked each time the Narya executable starts up.  It would be more efficient to parse and typecheck them when Narya is *compiled* and then store their .nyo versions here instead. *)

let visible = [%blob "hott-visible.ny"]
let isfibrant = [%blob "hott-isfibrant.ny"]
let hidden = [%blob "hott-hidden.ny"]

(* First we define some stripped-down versions of the batch file loading functions. *)

let rec batch p src =
  match ParserCommand.Parse.final p with
  | Eof -> ()
  | Bof _ ->
      let p, src = ParserCommand.Parse.restart_parse p src in
      batch p src
  | cmd ->
      let _ =
        ParserCommand.execute
          ~action_taken:(fun _ -> ())
          ~get_file:(fun _ -> fatal (Anomaly "can't load files during bootstrapping"))
          cmd in
      let p, src = ParserCommand.Parse.restart_parse p src in
      batch p src

let bootstrap title content =
  let title = Some title in
  let p, src = ParserCommand.Parse.start_parse (`String { title; content } : Asai.Range.source) in
  batch p src

(* For frobnicating things, we need to look up the defined terms that result from the bootstrapping. *)
let get name =
  match Scope.lookup name with
  | Some const -> const
  | None -> fatal (Anomaly (String.concat "." name ^ " not in scope"))

let install () =
  (* Load the visible bootstrap file, which defines isBisim and glue. *)
  bootstrap "visible bootstrap" visible;
  let glue = get [ "glue" ] in

  (* Mark glue as being glue. *)
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

  (* Load the hidden isfibrant bootstrap file *)
  let isfibrant_file = File.make (`Other "isfibrant bootstrap") in
  ( Origin.with_file ~holes_allowed:false isfibrant_file @@ fun () ->
    bootstrap "isfibrant bootstrap" isfibrant;

    (* Use this to compute the types of fibrancy fields. *)
    let isfibrant = get [ "isFibrant" ] in
    match Global.find isfibrant with
    | _, (`Defined (Lam (x, Canonical (Codata { eta = Noeta; dim; fields; _ }))), _) -> (
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
    | _ -> fatal (Anomaly "isFibrant has wrong shape") );

  (* Load the hidden bootstrap file.  This requires that types already *have* fibrancy fields, so it has to be a separate file from hott-isfibrant. *)
  let bootstrap_file = File.make (`Other "hidden bootstrap") in
  Origin.with_file ~holes_allowed:false bootstrap_file @@ fun () ->
  bootstrap "hidden bootstrap" hidden;

  (* To compute the fibrancy fields of a pi-type, we basically copy a minimal part of the code from the proof in binary parametricity that pi-types are fibrant, with a few changes.  First we typecheck a proof that fibrancy is preserved under retraction. *)
  let eq_trr = get [ "eq"; "trr" ] in
  let eq_trr2 = get [ "eq"; "trr2" ] in
  let id_rtr = get [ "Id_rtr" ] in
  let fib_rtr = get [ "fib_rtr" ] in
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
  (* Now we pull out the fields from the definition of fib_pi to insert them in Fibrancy.pi. *)
  let id_pi_rtr = get [ "id_pi_rtr" ] in
  let fib_pi = get [ "fib_pi" ] in
  (match Global.find fib_pi with
  | _, (`Defined (Lam (a, Lam (b, Struct { dim; fields; eta = Noeta; energy = Potential }))), _)
    -> (
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

  (* Fibrancy of glue types *)
  let glue_rtr = get [ "glue_rtr" ] in
  let fib_glue = get [ "fib_glue" ] in
  (match Global.find fib_glue with
  | ( _,
      ( `Defined
          (Lam
             (a, Lam (b, Lam (r, Lam (re, Struct { dim; fields; eta = Noeta; energy = Potential }))))),
        _ ) ) -> (
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
  match Global.find glue_rtr with
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
  | _ -> fatal (Anomaly "glue_rtr_rtr undefined")
