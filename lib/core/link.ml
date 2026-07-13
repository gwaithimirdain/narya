open Util
open Dim
open Term
open Origin

(* When "linking" a pre-compiled file with the current run, we need to walk the unmarshaled terms and replace the old autonumbers of files, from when the file was compiled, with the current ones. *)

let rec term : type mode a s. (File.t -> File.t) -> (mode, a, s) term -> (mode, a, s) term =
 fun f tm ->
  match tm with
  | Var i -> Var i
  | Const c -> Const (Constant.remake f c)
  | Meta (m, s) -> Meta (Meta.remake f m, s)
  | MetaEnv (m, e) -> MetaEnv (Meta.remake f m, env f e)
  | Field (Modal (modality, al, tm), fld, fldins) ->
      Field (Modal (modality, al, term f tm), fld, fldins)
  | UU (mode, n) -> UU (mode, n)
  | Inst (tm, args) -> Inst (term f tm, TubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ args ])
  | Pi { x; filter; doms = Modal (modality, al, doms); cods } ->
      Pi
        {
          x;
          filter;
          doms = Modal (modality, al, CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ doms ]);
          cods = CodCube.mmap { map = (fun _ [ Cod (filt, x) ] -> Cod (filt, term f x)) } [ cods ];
        }
  | App (fn, m, filter, Modal (modality, al, args)) ->
      App
        ( term f fn,
          m,
          filter,
          Modal (modality, al, CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ args ]) )
  | Constr (c, n, args) ->
      Constr
        ( c,
          n,
          List.map
            (fun (Term.Modal (filter, al, arg)) ->
              Modal (filter, al, CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ arg ]))
            args )
  | Act (tm, s, sort) -> Act (term f tm, s, sort)
  | Key v -> Key { v with tm = term f v.tm }
  | Let (x, Modal (modality, al, v), body) -> Let (x, Modal (modality, al, term f v), term f body)
  | Lam (x, p, filter, body) -> Lam (x, p, filter, term f body)
  | Struct { eta; dim; fields = flds; energy } ->
      Struct
        {
          eta;
          dim;
          fields =
            Mbwd.map
              (fun (Term.StructfieldAbwd.Entry (fld, x)) ->
                Term.StructfieldAbwd.Entry (fld, structfield f x))
              flds;
          energy;
        }
  | Match { tm; plus_lock; window; dim; branches } ->
      Match
        { tm = term f tm; plus_lock; window; dim; branches = Constr.Map.map (branch f) branches }
  | Realize tm -> Realize (term f tm)
  | Canonical can -> Canonical (canonical f can)
  | Unshift (n, plusmap, tm) -> Unshift (n, plusmap, term f tm)
  | Unact (o, tm) -> Unact (o, term f tm)
  | Shift (n, plusmap, tm) -> Shift (n, plusmap, term f tm)
  | Weaken tm -> Weaken (term f tm)

and branch : type mode a n. (File.t -> File.t) -> (mode, a, n) branch -> (mode, a, n) branch =
 fun f br ->
  match br with
  | Branch b -> Branch { b with tm = term f b.tm }
  | Refute -> Refute

and canonical : type mode a. (File.t -> File.t) -> (mode, a) canonical -> (mode, a) canonical =
 fun f can ->
  match can with
  | Data { indices; constrs; discrete; recursive; hints } ->
      Data
        {
          indices;
          constrs = Abwd.map (dataconstr f) constrs;
          discrete;
          recursive = Positivity.link_recursion f recursive;
          hints;
        }
  | Codata { eta; opacity; hints; dim; termctx = tc; fields; fibrancy = fib; is_glue } ->
      let trr =
        Mbwd.map
          (fun (StructfieldAbwd.Entry (fld, x)) -> StructfieldAbwd.Entry (fld, structfield f x))
          fib.trr in
      let liftr =
        Mbwd.map
          (fun (StructfieldAbwd.Entry (fld, x)) -> StructfieldAbwd.Entry (fld, structfield f x))
          fib.liftr in
      let trl =
        Mbwd.map
          (fun (StructfieldAbwd.Entry (fld, x)) -> StructfieldAbwd.Entry (fld, structfield f x))
          fib.trl in
      let liftl =
        Mbwd.map
          (fun (StructfieldAbwd.Entry (fld, x)) -> StructfieldAbwd.Entry (fld, structfield f x))
          fib.liftl in
      Codata
        {
          eta;
          opacity;
          hints;
          dim;
          termctx = Option.map (termctx f) tc;
          fields =
            Mbwd.map
              (fun (CodatafieldAbwd.Entry (fld, x)) -> CodatafieldAbwd.Entry (fld, codatafield f x))
              fields;
          fibrancy = { fib with ty = term f fib.ty; trr; trl; liftr; liftl };
          is_glue;
        }

and structfield : type mode n a s i et.
    (File.t -> File.t) ->
    (i, mode * (n * a * s * et)) Term.Structfield.t ->
    (i, mode * (n * a * s * et)) Term.Structfield.t =
 fun f fld ->
  match fld with
  | Lower (adj, plus_lock, tm, lbl) -> Lower (adj, plus_lock, term f tm, lbl)
  | Higher m ->
      Higher
        (PlusPbijmap.mmap
           {
             map =
               (fun _ [ x ] ->
                 match x with
                 | Some (PlusFam (rb, x)) -> Some (PlusFam (rb, term f x))
                 | None -> None);
           }
           [ m ])
  | LazyHigher _ -> Reporter.fatal (Anomaly "lazy higher field can't be linked")

and codatafield : type mode a n i et.
    (File.t -> File.t) ->
    (i, mode * a * n * et) Codatafield.t ->
    (i, mode * a * n * et) Codatafield.t =
 fun f fld ->
  match fld with
  | Lower (adj, plus_lock, ty) -> Lower (adj, plus_lock, term f ty)
  | Higher (ka, tm) -> Higher (ka, term f tm)

and dataconstr : type mode p i.
    (File.t -> File.t) -> (mode, p, i) dataconstr -> (mode, p, i) dataconstr =
 fun f (Dataconstr { args; indices }) ->
  Dataconstr { args = tel f args; indices = Vec.mmap (fun [ x ] -> term f x) [ indices ] }

and tel : type mode a b ab. (File.t -> File.t) -> (mode, a, b, ab) tel -> (mode, a, b, ab) tel =
 fun f t ->
  match t with
  | Emp -> Emp
  | Ext (x, Modal (modality, al, ty), t) -> Ext (x, Modal (modality, al, term f ty), tel f t)

and env : type mode a n b. (File.t -> File.t) -> (mode, a, n, b) env -> (mode, a, n, b) env =
 fun f e ->
  match e with
  | Emp (mode, n) -> Emp (mode, n)
  | Ext ({ env = e; values = Modal (modality, al, xs); _ } as ext) ->
      Ext
        {
          ext with
          env = env f e;
          values = Modal (modality, al, CubeOf.mmap { map = (fun _ [ x ] -> term f x) } [ xs ]);
        }
  | Key k -> Key { k with env = env f k.env }
  | Prekey k -> Prekey { k with env = env f k.env }

and entry : type dom modality mode b f mn bm.
    (File.t -> File.t) ->
    (dom, modality, mode, b, bm, f, mn) entry ->
    (dom, modality, mode, b, bm, f, mn) entry =
 fun f e ->
  match e with
  | Vis v ->
      let bindings =
        CubeOf.mmap
          {
            map =
              (fun _ [ (b : (dom, bm) binding) ] : (dom, bm) binding ->
                { ty = term f b.ty; tm = Option.map (term f) b.tm });
          }
          [ v.bindings ] in
      Vis { v with bindings }
  | Invis v ->
      let bindings =
        CubeOf.mmap
          {
            map =
              (fun _ [ (b : (dom, bm) binding) ] : (dom, bm) binding ->
                { ty = term f b.ty; tm = Option.map (term f) b.tm });
          }
          [ v.bindings ] in
      Invis { v with bindings }

and termctx_ordered : type mode a b.
    (File.t -> File.t) -> (mode, a, b) ordered_termctx -> (mode, a, b) ordered_termctx =
 fun f ctx ->
  match ctx with
  | Emp mode -> Emp mode
  | Ext (ctx, e, ax) -> Ext (termctx_ordered f ctx, entry f e, ax)
  | Lock (ctx, lock) -> Lock (termctx_ordered f ctx, lock)

and termctx : type mode a b. (File.t -> File.t) -> (mode, a, b) termctx -> (mode, a, b) termctx =
 fun f (Permute (p, ctx)) -> Permute (p, termctx_ordered f ctx)

let metadef : type mode x y z.
    (File.t -> File.t) -> (mode, x, y, z) Metadef.t -> (mode, x, y, z) Metadef.t =
 fun f data ->
  let termctx = termctx f data.termctx in
  let ty = term f data.ty in
  let tm =
    match data.tm with
    | `Defined tm -> `Defined (term f tm)
    | x -> x in
  let recursion = Positivity.link_recursion f data.recursion in
  { data with tm; termctx; ty; recursion }
