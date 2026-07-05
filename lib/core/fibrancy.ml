open Bwd
open Bwd.Infix
open Dim
open Modal
open Util
open Tbwd
open Tctx
open Term
open Monad.Ops (Monad.Maybe)

let other = (`Other, `Other)

(* Fibrancy fields *)

(* The names of the fibrancy fields. *)

let ([ ftrr; fliftr; ftrl; fliftl; fid ] : (Hott.dim Field.t, Fwn.five) Vec.t) =
  Vec.map (fun x -> Field.intern x Hott.dim) [ "trr"; "liftr"; "trl"; "liftl"; "id" ]

(* The types of the user-accessible, non-corecursive, fibrancy fields *)

(* We will later get these fields by typechecking the definition of "isFibrant" in parametric Narya.  That definition has a (non-fibrant) type as a parameter, so together with the self variable all of its fields are in a context of length two; and since the extension by the self variable is accounted for in the definition of Codatafield, what we get here is a context of length one.  However, in HOTT mode we consider (fibrant) types as *themselves* having fields, so the type itself should now act like the "self variable"; we will deal with this at the point of use by evaluating it in an environment with the fibrant type itself appearing for both the type parameter and the element of isFibrant.  The D.zero says that isFibrant is an ordinary (non-Gel) codatatype. *)

module Fields = struct
  type ('a, 'mode) t =
    ('mode * ('mode emp, ('mode id, D.zero) dim_entry) snoc * D.zero * no_eta) CodatafieldAbwd.t
end

module FieldsMap = Mode.Map.Make (Fields)

let fields : unit FieldsMap.t ref = ref FieldsMap.empty

(* Computing the fibrancy fields on canonical type-formers *)

(* The dimension 'n of these Structfields is almost always 0, since it is the substitution dimension of the type being checked against, and canonical types are almost always defined to belong to the 0-dimensional universe.  The one exception, of course, is Gel/glue, where this is the gel dimension.  When n=0, we are proving isFibrant; when n is larger we're proving "refl isFibrant" or some higher version of it.  *)

(* Pi-types *)

(* In the case of pi-types, we can literally write the definition in Narya, typecheck it, and insert it here.  That makes it easier to get correct.  Thus, for now we leave this empty; it will be filled in after the parser is loaded. *)

module PiValues = struct
  type ('a, 'dom, 'modality, 'mode) t =
    ('mode
    * (D.zero
      * (('mode emp, ('modality, D.zero) dim_entry) snoc, ('mode id, D.zero) dim_entry) snoc
      * potential
      * no_eta))
    StructfieldAbwd.t
end

module PiValuesMap = Modality.Map.Make (PiValues)

let pi : unit PiValuesMap.t ref = ref PiValuesMap.empty

(* Glue types *)

module GlueValues = struct
  type ('a, 'mode) t =
    ('mode
    * (Hott.dim
      * ( ( (('mode emp, ('mode id, D.zero) dim_entry) snoc, ('mode id, D.zero) dim_entry) snoc,
            ('mode id, D.zero) dim_entry )
          snoc,
          ('mode id, D.zero) dim_entry )
        snoc
      * potential
      * no_eta))
    StructfieldAbwd.t
end

module GlueValuesMap = Mode.Map.Make (GlueValues)

let glue : unit GlueValuesMap.t ref = ref GlueValuesMap.empty

(* Codata types *)

(* We compute these directly as terms.  This puts the onus on us to define them in a well-typed way, but we try our best to copy the definitions that can be given (and typechecked) internally using the higher coinductive isFibrant.  The outer laziness is only to delay them until we're inside Dim.Endpoints.run.  Eventually when the HOTT dimension is built-in and always present, that won't be necessary (but we will still need the LazyHigher wrapper around the 'id' field in some cases). *)

module Codata = struct
  type (_, _, _, _, _) t =
    | Fibrancy : ('mode, 'g, 'n, 'nh, 'b, 'hb, 'et) codata_fibrancy -> ('mode, 'g, 'n, 'b, 'et) t

  (* We compute the fibrancy fields of a codatatype progressively field-by-field as the codatatype declaration is typechecked, starting with an empty one and adding to it. *)

  let empty : type mode g n b et.
      g D.t ->
      n D.t ->
      (mode, b) Tctx.t ->
      (potential, et) eta ->
      (mode, b, kinetic) term ->
      (mode, g, n, b, et) t =
   fun glue dim length eta ty ->
    let (Exists (type hb) (plusmap : (Hott.dim, b, hb, mode) plusmap)) =
      plusmap_exists Hott.dim length in
    let (Plus dimh) = D.plus Hott.dim in
    Fibrancy
      { glue; dim; length; plusmap; ty; eta; dimh; trr = Emp; trl = Emp; liftr = Emp; liftl = Emp }

  (* Given the typechecked version of a field, add the corresponding behavior of the fibrancy fields. *)
  let add_field : type mode g n b et.
      mode Mode.t ->
      (mode, g, n, b, et) t ->
      (mode * b * g * et) CodatafieldAbwd.entry ->
      (mode, g, n, b, et) t =
   fun mode (Fibrancy (type nh hb) (f : (mode, g, n, nh, b, hb, et) codata_fibrancy))
       (Entry (fld, fldty)) ->
    (* x is the index-zero variable. *)
    let x = Var (Index (Now, id_sface D.zero, Modality.filter_id mode D.zero, plus_with_no_locks mode)) in
    let ins = zero_ins Hott.dim in
    (* Compute terms that project each fibrancy field out of the codatatype and apply it to the index-zero variable 'x'. *)
    let idm = Modality.id mode in
    let idf = Modality.filter_id mode Hott.dim in
    let onx : Hott.dim Field.t -> (mode, (hb, (mode id, D.zero) dim_entry) snoc, kinetic) term =
     fun trlift ->
      app
        (Field (Weaken (Shift (Hott.dim, f.plusmap, f.ty)), trlift, ins))
        idm (plus_no_lock mode) x in
    let trr_x, liftr_x, trl_x, liftl_x = (onx ftrr, onx fliftr, onx ftrl, onx fliftl) in
    (* xrcube and xlcube are 1-dimensional cubes consisting of the index-zero variable 'x' and its transports right or left. *)
    match (Hott.cube x trr_x liftr_x, Hott.cube trl_x x liftl_x) with
    | Some xrcube, Some xlcube ->
        (* This generic functions computes the specified field projection 'fld' of any of the fibrancy fields, by applying that fibrancy field to the corresponding 'fld' of the input. *)
        let trlift : type m.
            Hott.dim Field.t ->
            (Hott.dim, (mode, (hb, (mode id, D.zero) dim_entry) snoc, kinetic) term) CubeOf.t ->
            (mode * (m * (hb, (mode id, D.zero) dim_entry) snoc * potential * et))
            StructfieldAbwd.entry =
         fun trlift xcube ->
          match fldty with
          | Lower ty ->
              let sty =
                Shift
                  ( Hott.dim,
                    f.plusmap,
                    Lam
                      ( singleton_variables f.glue (`Anon no_hints),
                        f.glue,
                        Modality.filter_id mode f.glue,
                        ty ) ) in
              StructfieldAbwd.Entry
                ( fld,
                  Lower
                    ( Realize
                        (app
                           (Field
                              ( App
                                  (Weaken sty, Hott.dim, idf, Modal (idm, plus_no_lock mode, xcube)),
                                trlift,
                                ins ))
                           idm (plus_no_lock mode)
                           (Field (x, fld, ins_zero f.dim))),
                      `Labeled ) )
          | Higher _ ->
              let open Reporter in
              fatal ~severity:Asai.Diagnostic.Bug (Unimplemented "higher fields of transport")
         (* TODO: Once it's written, call this from Check.check_codata too. *)
         (* Entry (f, Higher _) *) in
        let new_trr, new_liftr, new_trl, new_liftl =
          (trlift ftrr xrcube, trlift fliftr xrcube, trlift ftrl xlcube, trlift fliftl xlcube) in
        Fibrancy
          {
            f with
            trr = Snoc (f.trr, new_trr);
            liftr = Snoc (f.liftr, new_liftr);
            trl = Snoc (f.trl, new_trl);
            liftl = Snoc (f.liftl, new_liftl);
          }
    | _ -> Fibrancy f

  (* After all the codatafields have been added, we can "finish" the job at the time of evaluation, combining the StructfieldAbwds for the four user fibrancy fields, and a computation of the corecursive field id, to produce a single StructfieldAbwd whose fields are the five fibrancy fields. *)
  let rec finish : type mode g n nh b hb et.
      mode Mode.t ->
      (mode * b * g * et) CodatafieldAbwd.t ->
      (mode, g, n, nh, b, hb, et) codata_fibrancy ->
      (mode * (g * b * potential * no_eta)) StructfieldAbwd.t =
   fun mode fields { glue; dim; length; plusmap; ty; eta; dimh; trr; trl; liftr; liftl } ->
    let idm = Modality.id mode in
    let xname = singleton_variables D.zero (`Named "x") in
    let yname = singleton_variables D.zero (`Named "y") in
    let plusfam x = Some (PlusFam.PlusFam (plusmap, x)) in
    let _pluszero x = Some (PlusFam.PlusFam (Plusmap.zerol length, x)) in
    (* Generic function combining trr and trl. *)
    let tr : type r.
        [ `Left | `Right ] ->
        (mode * (n * (hb, (mode id, D.zero) dim_entry) snoc * potential * et)) StructfieldAbwd.t ->
        (g, Hott.dim, r) pbij ->
        (r, mode * b) PlusFam.t =
     fun _which fields p ->
      match singleton_pbij p Hott.singleton with
      (* This is the "tr.e" case when we just pass off to the type of the field. *)
      | Left ->
          plusfam
            (Lam
               ( xname,
                 D.zero,
                 Modality.filter_id mode D.zero,
                 Struct { dim; eta; energy = Potential; fields } ))
      (* This is the tr.1/tr.2 case when we should use the bisimulation data supplied.  The insertion is an insertion into g, the glue dimension.  Currently we don't do anything here, however, because the only case when this could happen is for a glue type, and we deal with those specially by bootstrapping their fibrancy and insesrting it using the is_glue marker.  *)
      | Right _ins -> None in
    let trr = PlusPbijmap.build glue Hott.dim { build = (fun p -> tr `Right trr p) } in
    let trl = PlusPbijmap.build glue Hott.dim { build = (fun p -> tr `Left trl p) } in
    let dimh = D.plus_out dim dimh in
    (* Generic function combining liftr and liftl. *)
    let lift : type r.
        [ `Left | `Right ] ->
        (mode * (nh * (hb, (mode id, D.zero) dim_entry) snoc * potential * et)) StructfieldAbwd.t ->
        (g, Hott.dim, r) pbij ->
        (r, mode * b) PlusFam.t =
     fun _which fields p ->
      match singleton_pbij p Hott.singleton with
      | Left ->
          plusfam
            (Lam
               ( xname,
                 D.zero,
                 Modality.filter_id mode D.zero,
                 Struct { dim = dimh; eta; energy = Potential; fields } ))
      | Right _ins -> None in
    let liftr = PlusPbijmap.build glue Hott.dim { build = (fun p -> lift `Right liftr p) } in
    let liftl = PlusPbijmap.build glue Hott.dim { build = (fun p -> lift `Left liftl p) } in
    let id : type r. (g, Hott.dim, r) pbij -> (r, mode * b) PlusFam.t =
     fun p ->
      match singleton_pbij p Hott.singleton with
      | Left -> (
          match D.compare_zero glue with
          | Zero ->
              let hlength = Plusmap.cod Hott.dim plusmap in
              let hlength00 =
                Plusmap.Dom.suc
                  (Plusmap.Dom.suc hlength (Dim (D.zero, Modality.filter_zero idm)))
                  (Dim (D.zero, Modality.filter_zero idm)) in
              let makeidx v =
                Var (Index (v, id_sface D.zero, Modality.filter_id mode D.zero, plus_with_no_locks mode))
              in
              let x0 = makeidx (Later (Later Now)) in
              let x1 = makeidx (Later Now) in
              let x2 = makeidx Now in
              let* xtube = Hott.tube x0 x1 in
              let* xcube = Hott.cube x0 x1 x2 in
              let folder :
                  (mode
                  * ((hb, (mode id, D.zero) dim_entry) snoc, (mode id, D.zero) dim_entry) snoc
                  * g
                  * et)
                  CodatafieldAbwd.t
                  * ( mode,
                      g,
                      nh,
                      ((hb, (mode id, D.zero) dim_entry) snoc, (mode id, D.zero) dim_entry) snoc,
                      et )
                    t ->
                  (mode * b * g * et) CodatafieldAbwd.entry ->
                  (mode
                  * ((hb, (mode id, D.zero) dim_entry) snoc, (mode id, D.zero) dim_entry) snoc
                  * g
                  * et)
                  CodatafieldAbwd.t
                  * ( mode,
                      g,
                      nh,
                      ((hb, (mode id, D.zero) dim_entry) snoc, (mode id, D.zero) dim_entry) snoc,
                      et )
                    t =
               fun (fields, fib) (CodatafieldAbwd.Entry (fld, fldty)) ->
                match fldty with
                | Lower fldty ->
                    let xsname = singleton_variables D.zero (`Named "x") in
                    let idm = Modality.id mode in
                    let idf = Modality.filter_id mode Hott.dim in
                    let field =
                      CodatafieldAbwd.Entry
                        ( fld,
                          Lower
                            (Inst
                               ( App
                                   ( Weaken
                                       (Weaken
                                          (Weaken
                                             (Shift
                                                ( Hott.dim,
                                                  plusmap,
                                                  Lam
                                                    ( xsname,
                                                      D.zero,
                                                      Modality.filter_id mode D.zero,
                                                      fldty ) )))),
                                     Hott.dim,
                                     idf,
                                     Modal (idm, plus_no_lock mode, xcube) ),
                                 TubeOf.mmap { map = (fun _ [ x ] -> field x fld) } [ xtube ] )) )
                    in
                    (Snoc (fields, field), add_field mode fib field)
                | Higher _ ->
                    (* TODO *)
                    (fields, fib) in
              let x0 = makeidx (Later Now) in
              let x1 :
                  ( mode,
                    ((hb, (mode id, D.zero) dim_entry) snoc, (mode id, D.zero) dim_entry) snoc,
                    kinetic )
                  term =
                makeidx Now in
              let* xtube = Hott.tube x0 x1 in
              let fields, Fibrancy fib =
                Bwd.fold_left folder
                  ( Emp,
                    empty glue dimh hlength00 eta
                      (Inst (Weaken (Weaken (Shift (Hott.dim, plusmap, ty))), xtube)) )
                  fields in
              let fib = finish mode fields fib in
              plusfam
              @@ Lam
                   ( xname,
                     D.zero,
                     Modality.filter_id mode D.zero,
                     Lam
                       ( yname,
                         D.zero,
                         Modality.filter_id mode D.zero,
                         Struct { dim = glue; eta = Noeta; energy = Potential; fields = fib } ) )
          | Pos _ ->
              (* The bisim .id case.  Again, this would be only for glue, so we ignore it. *)
              None)
      | Right _ins ->
          (* Would also be only for glue. *)
          None in
    let id = lazy (PlusPbijmap.build glue Hott.dim { build = (fun p -> id p) }) in
    Emp
    <: StructfieldAbwd.Entry (ftrr, Higher trr)
    <: Entry (fliftr, Higher liftr)
    <: Entry (ftrl, Higher trl)
    <: Entry (fliftl, Higher liftl)
    <: Entry (fid, LazyHigher id)

  (* TODO: It would be nice to memoize the "finish" computation.  But we can't store it as a mutable field inside a Term, because it contains a LazyHigher and so is not marshalable.  Maybe we could use a hashtable, but it would be tricky to ensure the output types depend correctly on the input ones.  I guess we could have a mutable Map depending on 'n' and 'a' and then hashtables inside of that.  But then it starts to get questionable how much time would be saved.  Let's wait until we do some profiling and see if this is actually a pain point. *)
  let finished : type mode n c a nh ha et.
      mode Mode.t ->
      (mode, n, c, a, nh, ha, et) codata_args ->
      (mode * (n * a * potential * no_eta)) StructfieldAbwd.t =
   fun mode c ->
    (* Fibrancy of glue-types is bootstrapped later and saved to the ref above, so here we detect whether the type is glue and insert that value if so. *)
    match c.is_glue with
    | Some Glue -> (
        match GlueValuesMap.find_opt mode !glue with
        | None -> Emp
        | Some fields -> fields)
    | None -> finish mode c.fields c.fibrancy
end

let universe : type mode.
    mode Mode.t -> (mode * (D.zero * mode emp * potential * no_eta)) StructfieldAbwd.t option Lazy.t
    =
 fun _mode -> Lazy.from_val None

let data : unit option Lazy.t = Lazy.from_val None
