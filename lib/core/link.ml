open Util
open Dim
open Term
open Origin

(* When "linking" a pre-compiled file with the current run, we need to walk the unmarshaled terms and replace the old autonumbers of files, from when the file was compiled, with the current ones.  We do this in place, by mutating the origins of the constants and metavariables that occur in them (see Origin.make_canonical), so that the terms are not reallocated and keep any sharing they had when they were marshaled (see Readback.sharing).  A constant or metavariable that has already been linked is recognized by its origin, so it is never linked twice, even if it is reached more than once.

   For the same reason, we don't walk a shared subterm more than once.  The later occurrences of a term that readback shared are wrapped in a Share node that carries a number identifying it, so we remember the terms we have already walked by those numbers.  (OCaml can't hash values by their addresses, since the garbage collector moves them, and a structural hash is of little use since many different terms have the same structure.)  The first occurrence of a shared term is not wrapped, so it is walked separately from the wrapped ones (and again whenever a shared term that contains it is), which is harmless since linking is idempotent.  The numbers are different for all the Share nodes created in one run, hence for all those in one compiled file, but to be safe we also check that the term we remembered is physically the same one, on its untyped representation (Obj.repr) since the terms we compare have different static types; this is only a comparison, never a coercion. *)

let walked : (int, Obj.t) Hashtbl.t = Hashtbl.create 100

let already_walked (i : int) (x : Obj.t) =
  match Hashtbl.find_opt walked i with
  | Some y -> x == y
  | None -> false

let record_walked (i : int) (x : Obj.t) = Hashtbl.replace walked i x

let rec term : type mode a s. (File.t -> File.t) -> (mode, a, s) term -> unit =
 fun f tm ->
  match tm with
  | Var _ -> ()
  | Const c -> Constant.relink f c
  | Meta (m, _) -> Meta.relink f m
  | MetaEnv (m, e) ->
      Meta.relink f m;
      env f e
  | Field (_, Modal (_, _, tm), _, _) -> term f tm
  | UU _ -> ()
  | Inst (_, tm, args) ->
      term f tm;
      TubeOf.miter { it = (fun _ [ x ] -> term f x) } [ args ]
  | Pi { doms = Modal (_, _, doms); cods; _ } ->
      CubeOf.miter { it = (fun _ [ x ] -> term f x) } [ doms ];
      CodCube.miter { it = (fun _ [ Cod (_, x) ] -> term f x) } [ cods ]
  | App (_, fn, _, _, Modal (_, _, args)) ->
      term f fn;
      CubeOf.miter { it = (fun _ [ x ] -> term f x) } [ args ]
  | Constr (_, _, args) ->
      List.iter
        (fun (Term.Modal (_, _, arg)) -> CubeOf.miter { it = (fun _ [ x ] -> term f x) } [ arg ])
        args
  | Act (_, tm, _, _) -> term f tm
  | Key v -> term f v.tm
  | Let (_, Modal (_, _, v), body) ->
      term f v;
      term f body
  | Letonly { termctx = tc; env = e; tm = body; ty } ->
      termctx f tc;
      env f e;
      term f body;
      term f ty
  | Lam (_, _, _, body) -> term f body
  | Struct { fields = flds; _ } ->
      Mbwd.miter (fun [ Term.StructfieldAbwd.Entry (_, x) ] -> structfield f x) [ flds ]
  | Match { tm; motive; branches; _ } ->
      term f tm;
      Option.iter (term f) motive;
      Constr.Map.iter (fun _ br -> branch f br) branches
  | Realize tm -> term f tm
  | Canonical can -> canonical f can
  | Unshift (_, _, tm) -> term f tm
  | Unact (_, tm) -> term f tm
  | Shift (_, _, tm) -> term f tm
  | Weaken (_, tm, _) -> term f tm
  | Share (i, tm) ->
      if not (already_walked i (Obj.repr tm)) then (
        term f tm;
        record_walked i (Obj.repr tm))
  | Failed _ -> ()

and branch : type mode a n. (File.t -> File.t) -> (mode, a, n) branch -> unit =
 fun f br ->
  match br with
  | Branch b -> term f b.tm
  | Failed_branch -> ()

and canonical : type mode a. (File.t -> File.t) -> (mode, a) canonical -> unit =
 fun f can ->
  match can with
  | Data { constrs; recursive; tyfam; _ } ->
      Abwd.iter (fun _ c -> term f c) constrs;
      Positivity.link_recursion f recursive;
      term f tyfam
  | Codata { fields; fibrancy; _ } ->
      (match fibrancy with
      | None -> ()
      | Some fib ->
          let structfields flds =
            Mbwd.miter (fun [ StructfieldAbwd.Entry (_, x) ] -> structfield f x) [ flds ] in
          term f fib.ty;
          structfields fib.trr;
          structfields fib.trl;
          structfields fib.liftr;
          structfields fib.liftl);
      Mbwd.miter (fun [ CodatafieldAbwd.Entry (_, x) ] -> codatafield f x) [ fields ]

and structfield : type mode n a s i et.
    (File.t -> File.t) -> (i, mode * (n * a * s * et)) Term.Structfield.t -> unit =
 fun f fld ->
  match fld with
  | Lower (_, _, tm, _) -> term f tm
  | Higher (_, _, m) ->
      (* We relink the terms in place, so we can discard the rebuilt map. *)
      ignore
        (PlusPbijmap.mmap
           {
             map =
               (fun _ [ x ] ->
                 (match x with
                 | Some (PlusFam (_, x)) -> term f x
                 | None -> ());
                 x);
           }
           [ m ])
  | LazyHigher _ -> Reporter.fatal (Anomaly "lazy higher field can't be linked")

and codatafield : type mode a m n i et.
    (File.t -> File.t) -> (i, mode * a * m * n * et) Codatafield.t -> unit =
 fun f (Codatafield (_, _, _, fld)) ->
  match fld with
  | Lower ty -> term f ty
  | Higher (tc, tys) ->
      termctx f tc;
      ignore
        (FieldtypePbijmap.mmap
           {
             map =
               (fun _ [ (Fieldtype (_, ty) as x) ] ->
                 term f ty;
                 x);
           }
           [ tys ])

and env : type mode a n b. (File.t -> File.t) -> (mode, a, n, b) env -> unit =
 fun f e ->
  match e with
  | Emp _ -> ()
  | Ext { env = e; values = Modal (_, _, xs); _ } ->
      env f e;
      CubeOf.miter { it = (fun _ [ x ] -> term f x) } [ xs ]
  | Lock k -> env f k.env
  | Prekey k -> env f k.env

and entry : type dom modality mode b f mn bm.
    (File.t -> File.t) -> (dom, modality, mode, b, bm, f, mn) entry -> unit =
 fun f e ->
  let binding (b : (dom, bm) binding) =
    term f b.ty;
    Option.iter (term f) b.tm in
  match e with
  | Vis v -> CubeOf.miter { it = (fun _ [ b ] -> binding b) } [ v.bindings ]
  | Invis v -> CubeOf.miter { it = (fun _ [ b ] -> binding b) } [ v.bindings ]

and termctx_ordered : type mode a b. (File.t -> File.t) -> (mode, a, b) ordered_termctx -> unit =
 fun f ctx ->
  match ctx with
  | Emp _ -> ()
  | Ext (ctx, e, _) ->
      termctx_ordered f ctx;
      entry f e
  | Lock (ctx, _) -> termctx_ordered f ctx
  | Weaken (ctx, _) -> termctx_ordered f ctx

and termctx : type mode a b. (File.t -> File.t) -> (mode, a, b) termctx -> unit =
 fun f (Permute (_, ctx)) -> termctx_ordered f ctx

let metadef : type mode x y z. (File.t -> File.t) -> (mode, x, y, z) Metadef.t -> unit =
 fun f data ->
  termctx f data.termctx;
  term f data.ty;
  (match data.tm with
  | `Defined tm -> term f tm
  | _ -> ());
  Positivity.link_recursion f data.recursion

(* Forget the terms walked so far, at the end of linking a compiled file. *)
let reset () = Hashtbl.reset walked
