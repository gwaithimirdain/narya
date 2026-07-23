(* Apply a category-theoretic 2-functor on the 2-category of modalities to terms.

   Terms in [Term] are parametrized by a free category of modes and modalities (their tctx
   parameter is a morphism in that free category).  They depend covariantly on this parameter:
   given a functor F on the category of modalities, we can transport a term along F, replacing
   every modality annotation by its F-image and changing the parametrizing tctx consistently.

   Mathematically, we would normally think of this as transporting terms from *one* mode
   2-category along a 2-functor to a *different* mode 2-category.  However, Narya is only set
   up to have one mode 2-category at a time.  Therefore, we work with an endo-2-functor of that
   2-category.  This isn't a big deal, since to talk morally about multiple 2-categories we can
   simply take their disjoint union and consider it one 2-category, and then a functor from one
   component to another becomes an endo-2-functor that maps the first component to the second
   and leaves the second where it is.

   This file defines an ML-functor [Make] whose argument is a category-theoretic endo-2-functor
   [Modality -> Modality], producing a mutually recursive suite of [apply_*] functions, one per
   type in [Term].  In addition, any constants and metavariables appearing in a term also need
   to be translated to new modes, so [Make] takes another two module arguments that do this. *)

(* IMPORTANT NOTE: This file was written largely by Claude Opus 4.7, and it has not been
   reviewed line-by-line by a human.  (This accounts for its differences in style to the rest
   of the codebase.)  However, the strong guarantees provided by the static type information,
   along with a manual verification that it does not call Obj.magic or raise any unjustified
   exceptions, can give us fairly good confidence that it is correct. *)

open Util
open Tbwd
open Modal
open Dim
open Tctx
open Reporter
open Variables

(* ------------------------------------------------------------------ *)
(* Input signatures                                                   *)
(* ------------------------------------------------------------------ *)

(* A category-theoretic 2-functor on modalities. *)
module type Modal2Functor = sig
  (* We use destructive substitution ([:=]) so the [t]-type equalities with [Modality.t] propagate; otherwise OCaml does not see [F.Dom.t = Modality.t]. *)
  include Category.Functor with module Dom := Modality and module Cod := Modality

  (* How F acts on modal 2-cells: source and target modality witnesses + cell -> new cell. *)

  val apply_cell :
    ('dom, 'mu, 'cod, 'fdom, 'fmu, 'fcod) t ->
    ('dom, 'nu, 'cod, 'fdom, 'fnu, 'fcod) t ->
    ('dom, 'mu, 'nu, 'cod) Modalcell.t ->
    ('fdom, 'fmu, 'fnu, 'fcod) Modalcell.t
end

(* How F acts on metavariable identifiers.  The caller supplies F.Obj evidence (mode), a tctx
   value at the new mode and tctx parameters, and the original Meta.t; returns the new Meta.t.
   If the application does not allow metavariables in the terms to be translated, the function
   can just raise an exception.  *)
module type MetaExt = sig
  module F : Modal2Functor

  (* TODO: Um, wait, we need 'fa to be the image of 'a! *)
  val apply :
    ('mode, 'fmode) F.Obj.t ->
    ('fmode, 'fa) Tctx.t ->
    ('mode, 'x, 'a, 's) Meta.t ->
    ('fmode, 'x, 'fa, 's) Meta.t
end

(* Similarly, how F acts on constants.  Unlike metavariables, a translation function like this
   is not mandated by the types, because constants are not currently parametried by their
   modes.  But it is necessary to have, because constants do *have* modes. *)
module type ConstExt = sig
  val apply : Constant.t -> Constant.t
end

(* We also have to assume that the functor preserves nonparametricity. *)
module type FilterExt = sig
  module F : Modal2Functor

  val apply :
    ('dom, 'mu, 'cod, 'fdom, 'fmu, 'fcod) F.t ->
    ('dom, 'mu, 'cod, 'a, 'b) Modality.filter_dim ->
    ('fdom, 'fmu, 'fcod, 'a, 'b) Modality.filter_dim
end

(* ------------------------------------------------------------------ *)
(* The main parametrized module                                       *)
(* ------------------------------------------------------------------ *)

module Make
    (F : Modal2Functor)
    (FMeta : MetaExt with module F = F)
    (FConst : ConstExt)
    (FFilter : FilterExt with module F = F) =
struct
  (* ********** Quivermap from TEntry to Tctxcat ********** *)

  (* For each generating TEntry edge we record where it goes in Tctxcat (a path):
       - Dim  : single Dim entry, with F-image modality
       - Lock : the lock generator g; F acts on of_gen g, then [Lock] turns the result back
                into a tctx path consisting of Lock entries.
       - Proj : single Proj entry, with F-image mode *)
  module EntryMap = struct
    module Dom = TEntry
    module Cod = Tctxcat

    (* The induced object map on [ModeUnit].  Like F.Obj on Mode, identity on Unit. *)
    module Obj = struct
      module Dom = ModeUnit
      module Cod = ModeUnit

      type (_, _) t = Mode_obj : ('a, 'b) F.Obj.t -> ('a, 'b) t | Unit_obj : (unit, unit) t

      let dom : type a x. (a, x) t -> a Dom.t = function
        | Mode_obj fab -> Mode (F.Obj.dom fab)
        | Unit_obj -> Unit

      let cod : type a x. (a, x) t -> x Cod.t = function
        | Mode_obj fab -> Mode (F.Obj.cod fab)
        | Unit_obj -> Unit

      type _ exists = Exists : ('a, 'x) t -> 'a exists

      let exists : type a. a Dom.t -> a exists = function
        | Mode a ->
            let (Exists fab) = F.Obj.exists a in
            Exists (Mode_obj fab)
        | Unit -> Exists Unit_obj

      let uniq : type a x1 x2. (a, x1) t -> (a, x2) t -> (x1, x2) Eq.t =
       fun f1 f2 ->
        match (f1, f2) with
        | Mode_obj fab1, Mode_obj fab2 -> F.Obj.uniq fab1 fab2
        | Unit_obj, Unit_obj -> Eq
        (* These two cases are impossible, since unit is not a mode.  OCaml can't tell that by itself since Mode.t is abstract, so we use the proof exported by Mode that unit is not a mode.  *)
        | Unit_obj, Mode_obj fab -> Mode.not_unit (F.Obj.dom fab) Eq
        | Mode_obj fab, Unit_obj -> Mode.not_unit (F.Obj.dom fab) Eq
    end

    type (_, _, _, _, _, _) t =
      | Dim_e :
          ('dom1, 'modality1, 'mode1, 'dom2, 'modality2, 'mode2) F.t
          * 'n D.t
          * ('dom1, 'modality1, 'mode1, 'n, 'n) Modality.filter_dim
          -> ( 'mode1,
               ('modality1, 'n) dim_entry,
               'mode1,
               'mode2,
               ('mode2 Tctxcat.id, ('modality2, 'n) dim_entry) Tctxcat.suc,
               'mode2 )
             t
      | Lock_e :
          ('dom1, 'mu, 'cod1) Modality.gen
          * ('dom1, ('cod1 Modality.id, 'mu) Modality.suc, 'cod1, 'dom2, 'fmodality, 'cod2) F.t
          * ('dom2, 'fmodality, 'cod2, 'dom2, 'flocks, 'cod2) Lock.t
          -> ('dom1, 'mu lock_entry, 'cod1, 'dom2, 'flocks, 'cod2) t
      | Proj_e :
          ('mode1, 'mode2) F.Obj.t
          -> ('mode1, 'mode1 proj, unit, 'mode2, (unit Tctxcat.id, 'mode2 proj) Tctxcat.suc, unit) t

    let dom : type a m b x n y. (a, m, b, x, n, y) t -> (a, m, b) Dom.t = function
      | Dim_e (_, n, filt) -> Dim (n, filt)
      | Lock_e (g, _, _) -> Lock g
      | Proj_e fab -> Proj (F.Obj.dom fab)

    let cod : type a m b x n y. (a, m, b, x, n, y) t -> (x, n, y) Cod.t = function
      | Dim_e (fm, n, filt) ->
          let fmodality = F.cod fm in
          Tctxcat.suc (Tctxcat.id (Mode (Modality.tgt fmodality))) (Dim (n, FFilter.apply fm filt))
      | Lock_e (_, _, lock_ev) -> Lock.cod lock_ev
      | Proj_e fab -> Tctxcat.suc (Tctxcat.id Unit) (Proj (F.Obj.cod fab))

    let src : type a m b x n y. (a, m, b, x, n, y) t -> (a, x) Obj.t = function
      (* For Dim, TEntry src=tgt=mode, so we use F.tgt (the mode side of the modality). *)
      | Dim_e (fm, _, _) -> Mode_obj (F.tgt fm)
      | Lock_e (_, fm, _) -> Mode_obj (F.src fm)
      | Proj_e fab -> Mode_obj fab

    let tgt : type a m b x n y. (a, m, b, x, n, y) t -> (b, y) Obj.t = function
      | Dim_e (fm, _, _) -> Mode_obj (F.tgt fm)
      | Lock_e (_, fm, _) -> Mode_obj (F.tgt fm)
      | Proj_e _ -> Unit_obj

    type (_, _, _) exists = Exists : ('a, 'm, 'b, 'x, 'n, 'y) t -> ('a, 'm, 'b) exists

    let exists : type a m b. (a, m, b) Dom.t -> (a, m, b) exists = function
      | Dim (n, filt) ->
          let (Exists fm) = F.exists (Modality.filter_modality filt) in
          Exists (Dim_e (fm, n, filt))
      | Lock g ->
          let (Exists fm) = F.exists (Modality.of_gen g) in
          let fmodality = F.cod fm in
          let (Exists lock_ev) = Lock.exists fmodality in
          (* Force the existentials in lock_ev's Tctxcat side to unify with the Modality side via the Lockmap.Obj.t identity witnesses. *)
          let (Lockmap.Obj.Eq _) = Lock.src lock_ev in
          let (Lockmap.Obj.Eq _) = Lock.tgt lock_ev in
          Exists (Lock_e (g, fm, lock_ev))
      | Proj a ->
          let (Exists fab) = F.Obj.exists a in
          Exists (Proj_e fab)

    let uniq : type a m b x1 n1 y1 x2 n2 y2.
        (a, m, b, x1, n1, y1) t -> (a, m, b, x2, n2, y2) t -> (x1 * n1 * y1, x2 * n2 * y2) Eq.t =
     fun f1 f2 ->
      match (f1, f2) with
      | Dim_e (fm1, _, _), Dim_e (fm2, _, _) ->
          (* The path's source is uniquely determined by its shape and target. *)
          let Eq = Modality.src_uniq (F.dom fm1) (F.dom fm2) in
          let Eq = F.uniq fm1 fm2 in
          Eq
      | Lock_e (_, fm1, lk1), Lock_e (_, fm2, lk2) ->
          let Eq = F.uniq fm1 fm2 in
          let Eq = Lock.uniq lk1 lk2 in
          Eq
      | Proj_e fab1, Proj_e fab2 ->
          let Eq = F.Obj.uniq fab1 fab2 in
          Eq
  end

  (* ********** Induced functor on the free category [Tctxcat] ********** *)

  (* By the universal property of free categories, the [TEntry → Tctxcat] quivermap [EntryMap] extends uniquely to a functor [Tctxcat → Tctxcat].  This is the type-level connector between an original tctx and its F-image. *)
  module FT = Path.Hom (TEntry) (Tctxcat) (EntryMap)

  (* A type-level witness saying that the tctx [(mode, a)] maps under F to [(fmode, fa)]. *)
  type ('mode, 'a, 'fmode, 'fa) tctx_fmap = ('mode, 'a, unit, 'fmode, 'fa, unit) FT.t

  (* Apply F to a Tctx, returning the new Tctx together with the witness. *)
  type (_, _) ctx_image =
    | Ctx_image : ('fmode, 'fa) Tctx.t * ('mode, 'a, 'fmode, 'fa) tctx_fmap -> ('mode, 'a) ctx_image

  let apply_ctx : type mode a. (mode, a) Tctx.t -> (mode, a) ctx_image =
   fun ctx ->
    let (Exists fev) = FT.exists ctx in
    match FT.tgt fev with
    | Unit_obj -> Ctx_image (FT.cod fev, fev)
    | Mode_obj fm -> Mode.not_unit (F.Obj.dom fm) Eq

  (* ********** Extend a tctx_fmap by a single Dim_e edge ********** *)

  (* When we descend into a binder (Lam, Let, Pi codomain, etc.), the body's tctx is the original tctx extended on the source side by one Dim entry [(modality, n)].  We extend the input witness by a single [Dim_e] EntryMap and a [Tctxcat.comp] composing it with the existing F-image path. *)
  let extend_witness_dim : type mode a fmode fa dom modality fdom fmodality n.
      (mode, a, fmode, fa) tctx_fmap ->
      (dom, modality, mode, fdom, fmodality, fmode) F.t ->
      n D.t ->
      (dom, modality, mode, n, n) Modality.filter_dim ->
      ( mode,
        (a, (modality, n) dim_entry) snoc,
        fmode,
        (fa, (fmodality, n) dim_entry) snoc )
      tctx_fmap =
   fun witness fmod n filt ->
    Suc (witness, Dim_e (fmod, n, filt), Tctxcat.Suc (Zero, Dim (n, FFilter.apply fmod filt)))

  (* ********** Structural F-image of a modality and its lock path **********

     Given a [Lock.t] (a modality interpreted as a sequence of lock generators mapping to a
     Tctxcat path of Lock TEntries), jointly construct the F-image triple:
       - [fmod]: F.t for the whole modality
       - [flock_ev]: Lock.t for the F-image modality
       - [ft_mlock]: FT.t for the original Tctxcat lock path
     where [flock_ev] and [ft_mlock] share the same Cod path by construction.

     The idea: walk [lock_ev] recursively.  At each generator [g], compute the per-generator
     F-image (fmod_g, flock_g) via [F.exists] + [Lock.exists].  Compose fmod_g with the
     inner fmod_inner via [F.comp].  Build the outer ft_mlock by adding a [Lock_e] edge for
     [g] with [flock_g] as its per-gen Lock.t.  Build the outer flock_ev by Lock.comp with
     the same per-gen flock_g.  Both end up with the same flocks path. *)
  type (_, _, _, _) f_image_lock =
    | F_image_lock :
        ('dom, 'mu, 'mode, 'fdom, 'fmodality, 'fmode) F.t
        * ('fdom, 'fmodality, 'fmode, 'fdom, 'fpath, 'fmode) Lock.t
        * ('dom, 'mlock, 'mode, 'fdom, 'fpath, 'fmode) FT.t
        -> ('dom, 'mu, 'mode, 'mlock) f_image_lock

  let rec f_image_lock : type dom mu mode mlock.
      (dom, mu, mode, dom, mlock, mode) Lock.t -> (dom, mu, mode, mlock) f_image_lock =
   fun lock_ev ->
    match lock_ev with
    | Zero (Lockmap.Obj.Eq m_mode) ->
        let (Exists fab) = F.Obj.exists m_mode in
        let fmod = F.id fab in
        let fm_mode = F.Obj.cod fab in
        let flock_ev = Lock.Zero (Lockmap.Obj.Eq fm_mode) in
        let ft_mlock = FT.Zero (Mode_obj fab) in
        F_image_lock (fmod, flock_ev, ft_mlock)
    | Suc (inner_lock, Inject (Lock_lock g_outer), Tctxcat.Suc (Tctxcat.Zero, Lock _)) ->
        let (F_image_lock (fmod_inner, flock_inner, ft_mlock_inner)) = f_image_lock inner_lock in
        (* Per-gen F-image pieces. *)
        let (Exists fmod_g) = F.exists (Modality.of_gen g_outer) in
        (* Align fmod_g's Modality tgt with fmod_inner's Modality src (both = tgt of g_outer
           at the type level). *)
        let Eq = F.Obj.uniq (F.tgt fmod_g) (F.src fmod_inner) in
        let fmodality_g = F.cod fmod_g in
        let (Exists flock_g) = Lock.exists fmodality_g in
        let (Lockmap.Obj.Eq _) = Lock.src flock_g in
        let (Lockmap.Obj.Eq _) = Lock.tgt flock_g in
        (* Modality.comp evidence for composing single-gen [of_gen g_outer] (inner) with
           [m_inner] (outer) to give the full outer modality [(m_inner, g_outer) suc]. *)
        let dom_comp_ev : (_, _, _, _, _, _) Modality.comp = Suc (Zero, g_outer) in
        let (F.Comp (fmod_outer, fmod_cod_comp)) = F.comp fmod_g fmod_inner dom_comp_ev in
        (* Compose flock_g (inner) with flock_inner (outer) via Lock.comp, using the F-image
           Modality.comp evidence from F.comp's result. *)
        let (Lock.Comp (flock_outer, flock_outer_cod_comp)) =
          Lock.comp flock_g flock_inner fmod_cod_comp in
        (* Build outer ft_mlock: add a Lock_e edge carrying (g_outer, fmod_g, flock_g).
           The Cod.comp evidence is the same flock_outer_cod_comp from Lock.comp. *)
        let new_lock_e : (_, _, _, _, _, _) EntryMap.t = Lock_e (g_outer, fmod_g, flock_g) in
        let ft_mlock_outer = FT.Suc (ft_mlock_inner, new_lock_e, flock_outer_cod_comp) in
        F_image_lock (fmod_outer, flock_outer, ft_mlock_outer)

  (* ********** Structural F-image of a [Locks.t] **********

     Like [f_image_lock] but for a Locks.t (which walks a general TEntry path with both Dim
     and Lock entries, producing a Modality from the Lock entries' generators).  Jointly
     constructs the F-image triple:
       - [fmod]: F.t for the locks_ev's modality
       - [ft_c]: FT.t for the input TEntry path c_path
       - [flocks_ev]: Locks.t for the F-image TEntry path (= ft_c's Cod) with codomain
         modality = F.cod fmod
     all sharing existentials so the modality and fc_path types align statically. *)
  type (_, _, _, _) f_image_locks =
    | F_image_locks :
        ('dom, 'modality, 'mode, 'fdom, 'fmodality, 'fmode) F.t
        * ('dom, 'c_path, 'mode, 'fdom, 'fc_path, 'fmode) FT.t
        * ('fdom, 'fc_path, 'fmode, 'fdom, 'fmodality, 'fmode) Locks.t
        -> ('dom, 'modality, 'mode, 'c_path) f_image_locks

  let rec f_image_locks : type dom modality mode c_path.
      (dom, c_path, mode, dom, modality, mode) Locks.t ->
      (dom, modality, mode, c_path) f_image_locks =
   fun locks_ev ->
    match locks_ev with
    | Zero (Locksmap.Obj.Eq m_mode) ->
        let (Exists fab) = F.Obj.exists m_mode in
        let fm_mode = F.Obj.cod fab in
        F_image_locks (F.id fab, FT.Zero (Mode_obj fab), Locks.Zero (Locksmap.Obj.Eq fm_mode))
    | Suc (inner_locks_ev, Locks_dim (n, filt), Zero) ->
        let (F_image_locks (fmod_inner, ft_c_inner, flocks_inner)) = f_image_locks inner_locks_ev in
        let annote = Modality.filter_modality filt in
        let (Exists fmod_annote) = F.exists annote in
        let Eq = F.Obj.uniq (F.tgt fmod_annote) (F.src fmod_inner) in
        (* Add a Dim_e edge to ft_c, contributing one F-image Dim TEntry. *)
        let new_dim_e : (_, _, _, _, _, _) EntryMap.t = Dim_e (fmod_annote, n, filt) in
        let new_filt = FFilter.apply fmod_annote filt in
        let new_dim_ft_cod_comp : (_, _, _, _, _, _) Tctxcat.comp =
          Tctxcat.Suc (Tctxcat.Zero, Dim (n, new_filt)) in
        let ft_c_outer = FT.Suc (ft_c_inner, new_dim_e, new_dim_ft_cod_comp) in
        (* Add a Locks_dim edge to flocks_ev with identity modality contribution. *)
        let new_locks_dim : (_, _, _, _, _, _) Locksmap.t = Locks_dim (n, new_filt) in
        let flocks_ev_outer = Locks.Suc (flocks_inner, new_locks_dim, Zero) in
        F_image_locks (fmod_inner, ft_c_outer, flocks_ev_outer)
    | Suc (inner_locks_ev, Locks_lock g_outer, Suc (Zero, _)) ->
        let (F_image_locks (fmod_inner, ft_c_inner, flocks_inner)) = f_image_locks inner_locks_ev in
        let (Exists fmod_g) = F.exists (Modality.of_gen g_outer) in
        let Eq = F.Obj.uniq (F.tgt fmod_g) (F.src fmod_inner) in
        let fmodality_g = F.cod fmod_g in
        let (Exists flock_g) = Lock.exists fmodality_g in
        let (Lockmap.Obj.Eq _) = Lock.src flock_g in
        let (Lockmap.Obj.Eq _) = Lock.tgt flock_g in
        (* Modality.comp evidence for combining single-gen with inner_modality. *)
        let dom_comp_ev : (_, _, _, _, _, _) Modality.comp = Suc (Zero, g_outer) in
        let (F.Comp (fmod_outer, fmod_cod_comp)) = F.comp fmod_g fmod_inner dom_comp_ev in
        (* Tctxcat.comp evidence for combining flock_g's Cod path with ft_c_inner's Cod. *)
        let (Comp tctx_cod_comp) = Tctxcat.comp (Lock.cod flock_g) in
        let ft_c_outer = FT.Suc (ft_c_inner, Lock_e (g_outer, fmod_g, flock_g), tctx_cod_comp) in
        (* Convert per-gen Lock.t to per-gen Locks.t via [locks_lock], compose with
           [flocks_inner] using the same Tctxcat.comp evidence. *)
        let (Locks.Comp (flocks_ev_outer, flocks_cod_comp)) =
          Locks.comp (locks_lock flock_g) flocks_inner tctx_cod_comp in
        (* Both Cod.comp evidences (from F.comp and Locks.comp) compose the same modalities
           at the same source/inner/outer/target, so their composite modality is unique. *)
        let Eq = Modality.comp_uniq flocks_cod_comp fmod_cod_comp in
        F_image_locks (fmod_outer, ft_c_outer, flocks_ev_outer)

  (* ********** Apply F to plus_lock ********** *)

  type (_, _, _, _, _, _, _) plus_lock_image =
    | Plus_lock_image :
        ('dom, 'modality, 'mode, 'fdom, 'fmodality, 'fmode) F.t
        * ('fctx, 'fmode, 'fmodality, 'fdom, 'fnewctx) plus_lock
        * ('dom, 'newctx, 'fdom, 'fnewctx) tctx_fmap
        -> ('ctx, 'mode, 'modality, 'dom, 'newctx, 'fmode, 'fctx) plus_lock_image

  let apply_plus_lock : type ctx mode modality dom newctx fmode fctx.
      (mode, ctx, fmode, fctx) tctx_fmap ->
      (ctx, mode, modality, dom, newctx) plus_lock ->
      (ctx, mode, modality, dom, newctx, fmode, fctx) plus_lock_image =
   fun witness (Plus_lock (lock_ev, comp_ev)) ->
    (* Use [f_image_lock] to jointly construct [fmod] (F.t for the modality), [flock_ev]
       (Lock.t for the F-image modality), and [ft_mlock] (FT.t for the original Tctxcat lock
       path), all sharing the same Cod path by construction.  No runtime functoriality
       check is needed. *)
    let (F_image_lock (fmod, flock_ev, ft_mlock)) = f_image_lock lock_ev in
    (* Align fmod's existential output-mode with the witness's fmode. *)
    let witness_src =
      match FT.src witness with
      | Mode_obj f -> f
      | Unit_obj -> Mode.not_unit (Modality.tgt (Lock.dom lock_ev)) Eq in
    let Eq = F.Obj.uniq witness_src (F.tgt fmod) in
    (* Compose ft_mlock with the input witness using the existing comp_ev. *)
    let (Comp (ft_newctx, cod_comp_ev)) = FT.comp ft_mlock witness comp_ev in
    let new_plus_lock = Plus_lock (flock_ev, cod_comp_ev) in
    Plus_lock_image (fmod, new_plus_lock, ft_newctx)

  (* ********** Apply F to plus_with_locks ********** *)

  (* plus_with_locks is similar to plus_lock but the appended part is any tctx (not just
     locks) provided it starts with a lock or is empty.  Its plus_with_locks carries a
     [starts_with_lock_or_empty] tag, a Tctx.comp, and a Locks witness.  We map each one. *)
  type (_, _, _, _, _, _, _) plus_with_locks_image =
    | Plus_with_locks_image :
        ('dom, 'modality, 'mode, 'fdom, 'fmodality, 'fmode) F.t
        * ('fa, 'fmode, 'fmodality, 'fdom, 'fac) plus_with_locks
        * ('dom, 'ac, 'fdom, 'fac) tctx_fmap
        -> ('a, 'mode, 'modality, 'dom, 'ac, 'fmode, 'fa) plus_with_locks_image

  let apply_plus_with_locks : type a mode modality dom ac fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (a, mode, modality, dom, ac) plus_with_locks ->
      (a, mode, modality, dom, ac, fmode, fa) plus_with_locks_image =
   fun witness (Plus_with_locks (comp_ev, locks_ev)) ->
    (* Use [f_image_locks] to jointly construct fmod, ft_c, and the new Locks.t for fc_path,
       all sharing the same fmodality by construction.  No runtime functoriality check. *)
    let (F_image_locks (fmod, ft_c, new_locks_raw)) = f_image_locks locks_ev in
    (* Align fmod's existential target with the witness's fmode. *)
    let witness_src =
      match FT.src witness with
      | Mode_obj f -> f
      | Unit_obj -> Mode.not_unit (Modality.tgt (Locks.cod locks_ev)) Eq in
    let Eq = F.Obj.uniq witness_src (F.tgt fmod) in
    let (Comp (ft_ac, cod_comp_ev)) = FT.comp ft_c witness comp_ev in
    let new_pwl = Plus_with_locks (cod_comp_ev, new_locks_raw) in
    Plus_with_locks_image (fmod, new_pwl, ft_ac)

  (* ********** Apply F to a Modalcell.adjunction ********** *)

  (* An adjunction is F-imaged by applying F to its left and right modalities, and then
     transporting its unit/counit 2-cells (and the composition witnesses relating them to the
     left/right modalities) along F via [F.comp] and [F.apply_cell].  We expose the F.t
     witnesses for the left and right modalities too, since callers need them to F-image the
     plus_lock that a modal field's adjunction is packaged with. *)
  type (_, _, _, _) adjunction_image =
    | Adjunction_image :
        ('a, 'f, 'b, 'fa, 'ff, 'fb) F.t
        * ('b, 'g, 'a, 'fb, 'fg, 'fa) F.t
        * ('fa, 'ff, 'fg, 'fb) Modalcell.adjunction
        -> ('a, 'f, 'g, 'b) adjunction_image

  let apply_adjunction : type a f g b.
      (a, f, g, b) Modalcell.adjunction -> (a, f, g, b) adjunction_image =
   fun (Adjunction { left; right; right_left; unit; left_right; counit }) ->
    let (Exists flmod) = F.exists left in
    let (Exists frmod) = F.exists right in
    let Eq = F.Obj.uniq (F.tgt flmod) (F.src frmod) in
    let Eq = F.Obj.uniq (F.src flmod) (F.tgt frmod) in
    let (F.Comp (fgf_mod, new_right_left)) = F.comp flmod frmod right_left in
    let (F.Comp (ffg_mod, new_left_right)) = F.comp frmod flmod left_right in
    let fa_obj = F.tgt frmod in
    let fb_obj = F.tgt flmod in
    let new_unit = F.apply_cell (F.id fa_obj) fgf_mod unit in
    let new_counit = F.apply_cell ffg_mod (F.id fb_obj) counit in
    Adjunction_image
      ( flmod,
        frmod,
        Adjunction
          {
            left = F.cod flmod;
            right = F.cod frmod;
            right_left = new_right_left;
            unit = new_unit;
            left_right = new_left_right;
            counit = new_counit;
          } )

  (* ********** Commute F with plusmap ********** *)

  (* F acts only on lock entries (sending each generator to a Lock-path) and identifies dim
     entries (sending each [Dim (mu, n)] to a single-edge path [Dim (F mu, n)]).  Plusmap acts
     only on dim entries (sending each [Dim (mu, k)] to [Dim (mu, n+k)]) and is the identity on
     lock and proj entries.  So they commute: given a tctx-fmap [a → fa] and a plusmap [a → an],
     we can extract a plusmap [fa → fan] where [fan] is the F-image of [an].  Implemented by
     structural recursion on the plusmap, destructuring the corresponding outer edges of both
     witnesses (tctx-fmaps) at each step. *)
  let rec plusmap_commute : type mode fmode n a fa an fan.
      n D.t ->
      (mode, a, fmode, fa) tctx_fmap ->
      (n, a, an, mode) plusmap ->
      (mode, an, fmode, fan) tctx_fmap ->
      (n, fa, fan, fmode) plusmap =
   fun n fa_w pm fan_w ->
    match (pm, fa_w, fan_w) with
    | Zero (Eq _), _, _ -> (
        (* pm = identity forces source mode = unit; fa_w and fan_w must both be Zero. *)
        match (fa_w, fan_w) with
        | Zero (Mode_obj fab), _ -> Mode.not_unit (F.Obj.dom fab) Eq
        | _, Zero (Mode_obj fab) -> Mode.not_unit (F.Obj.dom fab) Eq
        | Zero Unit_obj, Zero Unit_obj -> Zero (Eq Unit))
    | ( Suc (pm_inner, Inject (Plus_dim (n_plus, nfilt, pfilt)), Suc (Zero, _)),
        Suc (fa_inner_w, Dim_e (fmod_a, _, _), Suc (Zero, _)),
        Suc (fan_inner_w, Dim_e (fmod_an, k_an, anfilt), Suc (Zero, _)) ) ->
        let Eq = Modality.src_uniq (F.dom fmod_a) (F.dom fmod_an) in
        let Eq = Modality.tgt_uniq (F.dom fmod_a) (F.dom fmod_an) in
        let Eq = F.uniq fmod_a fmod_an in
        let Eq, Eq = Modality.filter_dim_modes nfilt (F.dom fmod_a) in
        let pm_new_inner = plusmap_commute n fa_inner_w pm_inner fan_inner_w in
        Suc
          ( pm_new_inner,
            Inject (Plus_dim (n_plus, FFilter.apply fmod_a nfilt, FFilter.apply fmod_a pfilt)),
            Suc (Zero, Dim (k_an, FFilter.apply fmod_a anfilt)) )
    | ( Suc (pm_inner, Inject (Plus_lock g_pm), Suc (Zero, _)),
        Suc (fa_inner_w, Lock_e (g_a, fmod_a, lock_ev_a), fa_cev),
        Suc (fan_inner_w, Lock_e (g_an, fmod_an, lock_ev_an), fan_cev) ) ->
        (* Align pm's outer generator (g_pm) with fa_w's (g_a) so pm_inner's source mode
               unifies with fa_inner_w's source mode (both = Modality.Gen.tgt of the shared g). *)
        let Eq = Modality.Gen.tgt_uniq g_pm g_a in
        let Eq = Modality.Gen.tgt_uniq g_pm g_an in
        let Eq = F.uniq fmod_a fmod_an in
        let Eq = Lock.uniq lock_ev_a lock_ev_an in
        let pm_new_inner = plusmap_commute n fa_inner_w pm_inner fan_inner_w in
        (* [lock_pm] is the plusmap on the F-image lock path: Plusmap is the identity on
               lock entries, so it just retypes [lock_ev_a] as a plusmap on the same path. *)
        let lock_pm = Plusmap.lock lock_ev_a in
        (* Compose [lock_pm] (outer / source-side in Cod) with [pm_new_inner] (inner /
               target-side in Cod) using [fa_cev] as the Dom-composition evidence (=
               Tctxcat.comp evidence, since Plusmap's Dom is Tctxcat). *)
        let (Comp (output_plusmap, output_cod_comp)) = Plusmap.comp n pm_new_inner lock_pm fa_cev in
        (* Result has Cod = composite of [flocks_path] (n2) and [fan_inner] (n1).  Use
               [fan_cev] (same composition equals [fan]) to align via [Tctxcat.comp_uniq]. *)
        let Eq = Tctxcat.comp_uniq output_cod_comp fan_cev in
        output_plusmap
    | ( Suc (pm_inner, Inject (Plus_proj _), Suc (Zero, _)),
        Suc (fa_inner_w, Proj_e fab_a, Suc (Zero, _)),
        Suc (fan_inner_w, Proj_e fab_an, Suc (Zero, _)) ) ->
        let Eq = F.Obj.uniq fab_a fab_an in
        let pm_new_inner = plusmap_commute n fa_inner_w pm_inner fan_inner_w in
        let fmode_t = F.Obj.cod fab_a in
        Suc (pm_new_inner, Inject (Plus_proj fmode_t), Suc (Zero, Proj fmode_t))

  (* ********** Mutually recursive apply_* family ********** *)

  (* The recursive family below transports each term-formers and supporting type under F.
     For each input value with type parameters (mode, a, ...), we use the input
     [tctx_fmap] (and, for sub-types like modal_term, an additional F.t witness for the
     modality) to determine the output type parameters and construct the new value.

     The implementation handles:
       - All non-modal cases (Var, UU, Inst, Field, Act, Realize, etc.) structurally.
       - Modal cases (Lam, Pi codomain, App, Let) by applying F to the bound modality and
         extending the tctx_fmap via [extend_witness_dim] or [apply_plus_lock].
       - Key/Modalcell by delegating to [F.apply_cell].
       - Const by calling [FConst.apply] to transform constants if necessary
       - Meta/MetaEnv by calling [FMeta.apply] to obtain new metavariables with the new context.
       - Match/branch by composing tctx witnesses via FT.comp on a Tctx.bcomp.
       - Codata/datatypes (canonical, codata_args, codata_fibrancy, dataconstr, tel) by
         recursive descent.
       - termctx/ordered_termctx/entry/binding by descent on the well-typed context.

     Some of the more complex sub-types (StructfieldAbwd, CodatafieldAbwd, PlusPbijmap,
     CodCube) wrap a recursive Term/term inside additional Cube/Abwd/Pbijmap machinery; their
     apply functions thread the relevant tctx_fmap through these structures. *)

  (* The image of a modal_term packages the F.t witness for its modality (existential) and
     the new modal_term at the F-image parameters. *)
  type (_, _, _, _, _, _) modal_term_image =
    | Modal_term_image :
        ('dom, 'modality, 'mode, 'fdom, 'fmodality, 'fmode) F.t
        * ('fmode, 'fmodality, 'fa, 's) Term.modal_term
        -> ('mode, 'modality, 'a, 's, 'fmode, 'fa) modal_term_image

  type (_, _, _, _, _, _, _) modal_term_cube_image =
    | Modal_term_cube_image :
        ('dom, 'modality, 'mode, 'fdom, 'fmodality, 'fmode) F.t
        * ('n, 'fdom, 'fmodality, 'fmode, 'fa, 's) Term.modal_term_cube
        -> ('n, 'dom, 'modality, 'mode, 'a, 's, 'fmode * 'fa) modal_term_cube_image

  type (_, _, _, _, _, _, _) insert_image =
    | Insert_image :
        ('fa, 'fmodality, 'n, 'fan) insert * ('dom, 'modality, 'mode, 'fdom, 'fmodality, 'fmode) F.t
        -> ('mode, 'a, 'modality, 'n, 'an, 'fmode, 'fan) insert_image

  type (_, _, _, _, _, _) env_image =
    | Env_image :
        ('fmode, 'fa, 'n, 'fb) Term.env * ('mode, 'b, 'fmode, 'fb) tctx_fmap
        -> ('mode, 'a, 'n, 'b, 'fmode, 'fa) env_image

  type (_, _, _, _, _, _) tel_image =
    | Tel_image :
        ('fmode, 'fa, 'b, 'fab) Term.tel * ('mode, 'ab, 'fmode, 'fab) tctx_fmap
        -> ('mode, 'a, 'b, 'ab, 'fmode, 'fa) tel_image

  (* F-image of codata_fibrancy.  The output's [fhb] (= F-image of [hb]) is existential
     since F generally changes the tctx-shape; the input's [hb] is consumed and the output's
     [fhb] is freshly determined by the F-image of the plusmap's codomain. *)
  type (_, _, _, _, _, _, _, _, _) codata_fibrancy_image =
    | Codata_fibrancy_image :
        ('fmode, 'g, 'n, 'nh, 'fb, 'fhb, 'et) Term.codata_fibrancy
        -> ('mode, 'g, 'n, 'nh, 'b, 'hb, 'et, 'fmode, 'fb) codata_fibrancy_image

  (* F-image of codata_args.  The output's [fha] is the F-image of [ha] (= codata_fibrancy's
     [hb] under F), bound existentially.  [c] (termctx variable count) is preserved by F. *)
  type (_, _, _, _, _, _, _, _, _) codata_args_image =
    | Codata_args_image :
        ('fmode, 'n, 'c, 'fa, 'nh, 'fha, 'et) Term.codata_args
        -> ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et, 'fmode, 'fa) codata_args_image

  type (_, _, _, _, _) annotate_fwd_image =
    | Annotate_fwd_image :
        ('n, 'fmode, 'fannotations, 'fmode, 'fmode, 'fb, 'fmode) VarAnnotate.fwd_t
        -> ('mode, 'fmode, 'n, 'annotations, 'b) annotate_fwd_image

  (* Parallel walk of [annotate] and [comp]: both share the inner morph [b] (a path of dim
     entries).  Walking in lock-step gives us the F-image annotate, the F-image bcomp at the
     same fb, and a witness for the composite tctx [ab] (= a + b) under F. *)
  type (_, _, _, _, _, _, _, _) annotate_bcomp_image =
    | Annotate_bcomp_image :
        ('n, 'fmode, 'fannotations, 'fmode, 'fmode, 'fb, 'fmode) VarAnnotate.fwd_t
        * ('fmode, 'fb, 'fmode, 'fa, unit, 'fab) Tctx.bcomp
        * ('mode, 'ab, 'fmode, 'fab) tctx_fmap
        -> ('n, 'mode, 'fmode, 'annotations, 'b, 'a, 'fa, 'ab) annotate_bcomp_image

  type (_, _, _, _, _, _, _, _, _) entry_image =
    | Entry_image :
        ('dom, 'modality, 'mode, 'fdom, 'fmodality, 'fmode) F.t
        * ('fdom, 'fmodality, 'fmode, 'fb, 'fbm, 'f, 'mn) Term.entry
        -> ('dom, 'modality, 'mode, 'b, 'bm, 'f, 'mn, 'fmode, 'fb) entry_image

  let rec apply_term : type mode a fmode fa s.
      (mode, a, fmode, fa) tctx_fmap -> (mode, a, s) Term.term -> (fmode, fa, s) Term.term =
   fun witness tm ->
    match tm with
    | Const c -> Const (FConst.apply c)
    | UU (mode, n) ->
        let fmode_obj = FT.src witness in
        let mode_t =
          match fmode_obj with
          | Mode_obj fab -> F.Obj.cod fab
          | Unit_obj -> Mode.not_unit mode Eq in
        UU (mode_t, n)
    | Meta (m, e) ->
        let fmode_obj = FT.src witness in
        let fab =
          match fmode_obj with
          | Mode_obj fab -> fab
          | Unit_obj -> Mode.not_unit (Meta.mode m) Eq in
        let new_ctx = FT.cod witness in
        let new_m = FMeta.apply fab new_ctx m in
        Meta (new_m, e)
    | MetaEnv (m, env) ->
        let (Env_image (new_env, b_witness)) = apply_env witness env in
        let fmode_obj =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit (Meta.mode m) Eq in
        let new_b_ctx = FT.cod b_witness in
        let new_m = FMeta.apply fmode_obj new_b_ctx m in
        MetaEnv (new_m, new_env)
    | Field (mt, f, ins) ->
        let (Modal_term_image (_, new_mt)) = apply_modal_term witness mt in
        Field (new_mt, f, ins)
    | Inst (ty, tube) ->
        let new_ty = apply_term witness ty in
        let new_tube = TubeOf.mmap { map = (fun _ [ x ] -> apply_term witness x) } [ tube ] in
        Inst (new_ty, new_tube)
    | Act (t, deg, sort) -> Act (apply_term witness t, deg, sort)
    | Lam (vars, n, filt, body) ->
        let k = dim_variables vars in
        let modality = Modality.filter_modality filt in
        let (Exists fmod) = F.exists modality in
        (* Align the existential [$fmode] of [fmod] with the [fmode] of the witness. *)
        let witness_src_obj =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit (Modality.tgt modality) Eq in
        let Eq = F.Obj.uniq witness_src_obj (F.tgt fmod) in
        let new_witness = extend_witness_dim witness fmod k (Modality.filter_idempotent filt) in
        let new_body = apply_term new_witness body in
        Lam (vars, n, FFilter.apply fmod filt, new_body)
    | Realize t -> Realize (apply_term witness t)
    | Unact (op, t) -> Unact (op, apply_term witness t)
    | App (fn, m, filter, args) ->
        let new_fn = apply_term witness fn in
        let (Modal_term_cube_image (fmod, new_args)) = apply_modal_term_cube witness args in
        App (new_fn, m, FFilter.apply fmod filter, new_args)
    | Pi { x; filter; doms; cods } ->
        let new_dom_image = apply_modal_term_cube witness doms in
        let (Modal_term_cube_image (fmod, doms)) = new_dom_image in
        let filter = FFilter.apply fmod filter in
        let cods = apply_cod_cube witness fmod cods in
        Pi { x; filter; doms; cods }
    | Constr (c, n, args_list) ->
        let new_args_list = List.map (apply_any_modal_term_cube witness) args_list in
        Constr (c, n, new_args_list)
    | Let (name, mt, body) ->
        let (Modal_term_image (fmod, new_mt)) = apply_modal_term witness mt in
        let new_witness =
          extend_witness_dim witness fmod D.zero (Modality.filter_zero (F.dom fmod)) in
        let new_body = apply_term new_witness body in
        Let (name, new_mt, new_body)
    | Var (Index (insert_ev, sface, filt, plus_wl_ev)) ->
        let (Plus_with_locks (comp_ev, _)) = plus_wl_ev in
        let (Uncomp (ft_an, _, _)) = FT.uncomp comp_ev witness in
        let (Plus_with_locks_image (fmod_pl, new_plus_wl, ft_newctx)) =
          apply_plus_with_locks ft_an plus_wl_ev in
        let (Insert_image (new_insert, fmod_ins)) = apply_insert ft_an insert_ev in
        let Eq = Modality.src_uniq (F.dom fmod_ins) (F.dom fmod_pl) in
        let Eq = F.uniq fmod_ins fmod_pl in
        let witness_src_obj =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit (Modality.src (Modality.filter_modality filt)) Eq in
        let Eq = F.Obj.uniq witness_src_obj (F.src fmod_pl) in
        (* The new_plus_with_locks's [fnewctx] should equal the outer [fa]; align via FT.uniq. *)
        let Eq = FT.uniq ft_newctx witness in
        let new_filt = FFilter.apply fmod_ins filt in
        Var (Index (new_insert, sface, new_filt, new_plus_wl))
    | Key { tm; cell; plus_tgt; plus_src } ->
        let (Plus_with_locks (comp_ev_tgt, _)) = plus_tgt in
        let (Uncomp (ft_a, _, _)) = FT.uncomp comp_ev_tgt witness in
        let (Plus_lock_image (fmod_src, new_plus_src, ft_am)) = apply_plus_lock ft_a plus_src in
        let (Plus_with_locks_image (fmod_tgt, new_plus_tgt, ft_ac_new)) =
          apply_plus_with_locks ft_a plus_tgt in
        (* Both fmod_src and fmod_tgt share source-mode (mu's source = nu's source = cod) and target-mode (mu's target = nu's target = mode).  Align their F-image source and target modes via F.Obj.uniq. *)
        let Eq = F.Obj.uniq (F.src fmod_src) (F.src fmod_tgt) in
        let Eq = F.Obj.uniq (F.tgt fmod_src) (F.tgt fmod_tgt) in
        let new_cell = F.apply_cell fmod_src fmod_tgt cell in
        let new_tm = apply_term ft_am tm in
        let Eq = FT.uniq ft_ac_new witness in
        Key { tm = new_tm; cell = new_cell; plus_tgt = new_plus_tgt; plus_src = new_plus_src }
    | Struct args ->
        let new_args = apply_struct_args witness args in
        Struct new_args
    | Match { window = _; plus_lock; tm; dim; branches } ->
        let (Plus_lock_image (_, new_plus_lock, new_witness)) = apply_plus_lock witness plus_lock in
        let new_window = plus_lock_modality new_plus_lock in
        let new_tm = apply_term new_witness tm in
        let new_branches = Constr.Map.map (apply_branch witness) branches in
        Match
          {
            window = new_window;
            plus_lock = new_plus_lock;
            tm = new_tm;
            dim;
            branches = new_branches;
          }
    | Canonical c -> Canonical (apply_canonical witness c)
    | Unshift (n, plusmap, inner) -> (
        let (Anyplus.Obj.Eq plusmap_mode_mu) = Plusmap.src plusmap in
        match plusmap_mode_mu with
        | Unit -> fatal (Anomaly "apply_term: Unshift has no mode")
        | Mode plusmap_mode_t -> (
            let nb_tctx = Plusmap.cod n plusmap in
            let (Exists ft_nb) = FT.exists nb_tctx in
            match FT.tgt ft_nb with
            | Mode_obj fab -> Mode.not_unit (F.Obj.dom fab) Eq
            | Unit_obj ->
                let ft_nb_src =
                  match FT.src ft_nb with
                  | Mode_obj f -> f
                  | Unit_obj -> Mode.not_unit plusmap_mode_t Eq in
                let witness_src =
                  match FT.src witness with
                  | Mode_obj f -> f
                  | Unit_obj -> Mode.not_unit plusmap_mode_t Eq in
                let Eq = F.Obj.uniq ft_nb_src witness_src in
                let new_inner = apply_term ft_nb inner in
                let new_plusmap = plusmap_commute n witness plusmap ft_nb in
                Unshift (n, new_plusmap, new_inner)))
    | Shift (n, plusmap, inner) -> (
        let (Anyplus.Obj.Eq plusmap_mode_mu) = Plusmap.src plusmap in
        match plusmap_mode_mu with
        | Unit -> fatal (Anomaly "apply_term: Shift has no mode")
        | Mode plusmap_mode_t -> (
            let b_tctx = Plusmap.dom plusmap in
            let (Exists ft_b) = FT.exists b_tctx in
            match FT.tgt ft_b with
            | Mode_obj fab -> Mode.not_unit (F.Obj.dom fab) Eq
            | Unit_obj ->
                let ft_b_src =
                  match FT.src ft_b with
                  | Mode_obj f -> f
                  | Unit_obj -> Mode.not_unit plusmap_mode_t Eq in
                let witness_src =
                  match FT.src witness with
                  | Mode_obj f -> f
                  | Unit_obj -> Mode.not_unit plusmap_mode_t Eq in
                let Eq = F.Obj.uniq ft_b_src witness_src in
                let new_inner = apply_term ft_b inner in
                let new_plusmap = plusmap_commute n ft_b plusmap witness in
                Shift (n, new_plusmap, new_inner)))
    | Weaken inner ->
        (* The input tctx is [(b, (modality, n) dim_entry) snoc].  The witness for it must be
           an FT.Suc whose last edge is a [Dim_e]; we pattern-match the Tctxcat.comp evidence
           as [Suc (Zero, _)] (the structurally-mandated shape for a single-Dim image path),
           which lets OCaml infer the composed Cod-shape. *)
        let (Suc (inner_witness, Dim_e (_, _, _), Tctxcat.Suc (Tctxcat.Zero, _))) = witness in
        Weaken (apply_term inner_witness inner)

  and apply_modal_term : type mode modality a s fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (mode, modality, a, s) Term.modal_term ->
      (mode, modality, a, s, fmode, fa) modal_term_image =
   fun witness (Modal (_modality, plus_lock_ev, body)) ->
    let (Plus_lock_image (fmod, new_plus_lock, new_witness)) =
      apply_plus_lock witness plus_lock_ev in
    let fmodality = F.cod fmod in
    let new_body = apply_term new_witness body in
    Modal_term_image (fmod, Modal (fmodality, new_plus_lock, new_body))

  and apply_modal_term_cube : type n dom modality mode a s fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (n, dom, modality, mode, a, s) Term.modal_term_cube ->
      (n, dom, modality, mode, a, s, fmode * fa) modal_term_cube_image =
   fun witness (Modal (_modality, plus_lock_ev, cube)) ->
    let (Plus_lock_image (fmod, new_plus_lock, new_witness)) =
      apply_plus_lock witness plus_lock_ev in
    let fmodality = F.cod fmod in
    let new_cube = Dim.CubeOf.mmap { map = (fun _ [ t ] -> apply_term new_witness t) } [ cube ] in
    Modal_term_cube_image (fmod, Modal (fmodality, new_plus_lock, new_cube))

  and apply_any_modal_term_cube : type n mode a s fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (n, mode, a, s) Term.any_modal_term_cube ->
      (n, fmode, fa, s) Term.any_modal_term_cube =
   fun witness (Modal (filter, plus_lock_ev, cube)) ->
    let (Plus_lock_image (fmod, new_plus_lock, new_witness)) =
      apply_plus_lock witness plus_lock_ev in
    let filter = FFilter.apply fmod filter in
    let new_cube = Dim.CubeOf.mmap { map = (fun _ [ t ] -> apply_term new_witness t) } [ cube ] in
    Modal (filter, new_plus_lock, new_cube)

  (* Apply F to a [CodCube] (cube of codomain bodies for a Pi-type).  Each cube position holds
     a body whose tctx is the surrounding tctx extended by [(modality, k) dim_entry] for the
     face's dimension [k].  We extend the witness by a Dim_e of the F-image modality at each
     face. *)
  and apply_cod_cube : type n dom modality mode a fmode fa fdom fmodality.
      (mode, a, fmode, fa) tctx_fmap ->
      (dom, modality, mode, fdom, fmodality, fmode) F.t ->
      (n, dom * modality * mode * a) Term.CodCube.t ->
      (n, fdom * fmodality * fmode * fa) Term.CodCube.t =
   fun witness fmod cube ->
    Term.CodCube.mmap
      {
        map =
          (fun face [ Term.CodFam.Cod (filt, body) ] ->
            let n_face = Dim.dom_sface face in
            let k = Modality.filtered n_face filt in
            let witness' = extend_witness_dim witness fmod k (Modality.filter_idempotent filt) in
            Term.CodFam.Cod (FFilter.apply fmod filt, apply_term witness' body));
      }
      [ cube ]

  and apply_insert : type mode a modality n an fmode fan.
      (mode, an, fmode, fan) tctx_fmap ->
      (a, modality, n, an) insert ->
      (mode, a, modality, n, an, fmode, fan) insert_image =
   fun witness insert_ev ->
    match insert_ev with
    | Now ->
        let (Suc (_, Dim_e (fmod, _, _), Tctxcat.Suc (Tctxcat.Zero, _))) = witness in
        Insert_image (Now, fmod)
    | Later inner_insert ->
        let (Suc (inner_witness, Dim_e (_, _, _), Tctxcat.Suc (Tctxcat.Zero, _))) = witness in
        let (Insert_image (inner_new_insert, fmod)) = apply_insert inner_witness inner_insert in
        Insert_image (Later inner_new_insert, fmod)

  and apply_env : type mode a n b fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (mode, a, n, b) Term.env ->
      (mode, a, n, b, fmode, fa) env_image =
   fun witness env ->
    match env with
    | Emp (mode, n) ->
        (* Emp has b = mode emp = (unit Tctxcat.id, mode proj) Tctxcat.suc.  Construct the
           b-witness from a Proj_e edge atop a Zero(Unit) base, with a single-Proj Tctxcat.comp. *)
        let fab =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit mode Eq in
        let fmode_t = F.Obj.cod fab in
        let proj_edge : (_, _ proj, unit, _, _, unit) EntryMap.t = Proj_e fab in
        let b_witness :
            ( _,
              (unit Tctxcat.id, _ proj) Tctxcat.suc,
              unit,
              _,
              (unit Tctxcat.id, _ proj) Tctxcat.suc,
              unit )
            FT.t =
          Suc (Zero Unit_obj, proj_edge, Tctxcat.Suc (Tctxcat.Zero, Proj fmode_t)) in
        Env_image (Emp (fmode_t, n), b_witness)
    | Ext { env = inner_env; filtered; filter; plus; values } ->
        let (Env_image (new_inner_env, b_witness)) = apply_env witness inner_env in
        let (Modal_term_cube_image (fmod, new_values)) = apply_modal_term_cube witness values in
        let k = D.plus_right plus in
        let new_b_witness = extend_witness_dim b_witness fmod k filtered in
        Env_image
          ( Ext
              {
                env = new_inner_env;
                filtered = FFilter.apply fmod filtered;
                filter = FFilter.apply fmod filter;
                plus;
                values = new_values;
              },
            new_b_witness )
    | Key { env; cell; plus_tgt; plus_src } ->
        let (Plus_with_locks (comp_ev_tgt, _)) = plus_tgt in
        let (Uncomp (ft_a, _, _)) = FT.uncomp comp_ev_tgt witness in
        let (Env_image (new_inner_env, b_witness)) = apply_env ft_a env in
        let (Plus_lock_image (fmod_src, new_plus_src, ft_bmu)) =
          apply_plus_lock b_witness plus_src in
        let (Plus_with_locks_image (fmod_tgt, new_plus_tgt, ft_ac_new)) =
          apply_plus_with_locks ft_a plus_tgt in
        let Eq = F.Obj.uniq (F.src fmod_src) (F.src fmod_tgt) in
        let Eq = F.Obj.uniq (F.tgt fmod_src) (F.tgt fmod_tgt) in
        let new_cell = F.apply_cell fmod_src fmod_tgt cell in
        let Eq = FT.uniq ft_ac_new witness in
        Env_image
          ( Key
              {
                env = new_inner_env;
                cell = new_cell;
                plus_tgt = new_plus_tgt;
                plus_src = new_plus_src;
              },
            ft_bmu )
    | Prekey { env; cell; plus_src; plus_tgt } ->
        let (Plus_with_locks (comp_ev_tgt, _)) = plus_tgt in
        let (Uncomp (ft_a, _, _)) = FT.uncomp comp_ev_tgt witness in
        let (Plus_lock_image (fmod_src, new_plus_src, ft_asrc)) = apply_plus_lock ft_a plus_src in
        let (Plus_with_locks_image (fmod_tgt, new_plus_tgt, ft_atgt_new)) =
          apply_plus_with_locks ft_a plus_tgt in
        let Eq = F.Obj.uniq (F.src fmod_src) (F.src fmod_tgt) in
        let Eq = F.Obj.uniq (F.tgt fmod_src) (F.tgt fmod_tgt) in
        let new_cell = F.apply_cell fmod_src fmod_tgt cell in
        let Eq = FT.uniq ft_atgt_new witness in
        let (Env_image (new_inner_env, b_witness)) = apply_env ft_asrc env in
        Env_image
          ( Prekey
              {
                env = new_inner_env;
                cell = new_cell;
                plus_src = new_plus_src;
                plus_tgt = new_plus_tgt;
              },
            b_witness )

  and apply_tel : type mode a b ab fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (mode, a, b, ab) Term.tel ->
      (mode, a, b, ab, fmode, fa) tel_image =
   fun witness tel ->
    match tel with
    | Emp -> Tel_image (Emp, witness)
    | Ext (name, mt, rest) ->
        let (Modal_term_image (fmod, new_mt)) = apply_modal_term witness mt in
        let next_witness =
          extend_witness_dim witness fmod D.zero (Modality.filter_zero (F.dom fmod)) in
        let (Tel_image (new_rest, final_witness)) = apply_tel next_witness rest in
        Tel_image (Ext (name, new_mt, new_rest), final_witness)

  and apply_dataconstr : type mode p i fmode fp.
      (mode, p, fmode, fp) tctx_fmap ->
      (mode, p, i) Term.dataconstr ->
      (fmode, fp, i) Term.dataconstr =
   fun witness (Dataconstr { args; indices }) ->
    let (Tel_image (new_args, pa_witness)) = apply_tel witness args in
    let new_indices = Vec.map (apply_term pa_witness) indices in
    Dataconstr { args = new_args; indices = new_indices }

  and apply_branch : type mode a n fmode fa.
      (mode, a, fmode, fa) tctx_fmap -> (mode, a, n) Term.branch -> (fmode, fa, n) Term.branch =
   fun witness br ->
    match br with
    | Refute -> Refute
    | Branch { annotate; comp; perm; tm } -> (
        let mode_value : mode Mode.t =
          match annotate with
          | Zero (VarAnnotator.Obj.Eq m) -> m
          | Suc (VarAnnotator.Annotate filt, _) -> Modality.tgt (Modality.filter_modality filt)
        in
        let fab =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit mode_value Eq in
        (* Walk [annotate] and [comp] in parallel — they share the inner morph [b], a path
           of dim entries only. *)
        let (Annotate_bcomp_image (new_annotate, new_comp, ab_witness)) =
          apply_annotate_bcomp witness fab annotate comp in
        (* Derive a witness for the body's tctx [c]: extract the [ab] tctx path from
           [ab_witness], apply [perm_dom] to get the [c] path, then use [FT.exists]. *)
        let ab_tctx = FT.dom ab_witness in
        let c_tctx = perm_dom perm ab_tctx in
        let (Exists c_witness_raw) = FT.exists c_tctx in
        let c_ft_src =
          match FT.src c_witness_raw with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit mode_value Eq in
        let Eq = F.Obj.uniq c_ft_src fab in
        match FT.tgt c_witness_raw with
        | Mode_obj fab_tgt -> Mode.not_unit (F.Obj.dom fab_tgt) Eq
        | Unit_obj ->
            let new_tm = apply_term c_witness_raw tm in
            (* Walk [perm] structurally to produce its F-image, threading [c_witness_raw]
                and [ab_witness] for entry-by-entry F.t lookups.  Handles [Id], [Insert]
                (Now and Later), and [Lock]. *)
            let new_perm = apply_perm mode_value c_witness_raw ab_witness perm in
            Branch { annotate = new_annotate; comp = new_comp; perm = new_perm; tm = new_tm })

  (* Walk [perm : (c, ab) permute] in parallel with the witnesses for [c] and [ab], producing
     [(fc, fab) permute].  At [Id], use [FT.uniq] to derive [fc = fab].  At [Insert] / [Lock],
     fall through to the appropriate witness Suc structure to F-image the modalities. *)
  and apply_perm : type mode c ab fmode fc fab.
      mode Mode.t ->
      (mode, c, unit, fmode, fc, unit) FT.t ->
      (mode, ab, unit, fmode, fab, unit) FT.t ->
      (c, ab) permute ->
      (fc, fab) permute =
   fun mode_value c_witness ab_witness p ->
    match p with
    | Id ->
        let Eq = FT.uniq c_witness ab_witness in
        Id
    | Insert (inner_perm, insert_ev) ->
        apply_perm_insert mode_value c_witness ab_witness inner_perm insert_ev
    | Lock inner_perm -> apply_perm_lock mode_value c_witness ab_witness inner_perm

  (* Walk [perm.Insert (inner_perm, insert_ev)] by destructuring [c_witness] (which has a
     [Dim_e] on top corresponding to perm's top dim_entry) and walking [insert_ev] through
     [ab_witness] to find the inserted dim_entry's position.  For both [Now] (insertion at
     the top) and [Later] (deeper insertion), we recurse appropriately. *)
  and apply_perm_insert : type mode c' x n ab fmode fc fab inner_b.
      mode Mode.t ->
      (mode, (c', (x, n) dim_entry) snoc, unit, fmode, fc, unit) FT.t ->
      (mode, ab, unit, fmode, fab, unit) FT.t ->
      (c', inner_b) permute ->
      (inner_b, x, n, ab) insert ->
      (fc, fab) permute =
   fun mode_value c_witness ab_witness inner_perm insert_ev ->
    match insert_ev with
    | Now -> (
        (* ab = (inner_b, dim_entry) snoc with inner_b = c'.  Both c_witness and ab_witness
           have a [Dim_e] for the same dim_entry on top.  Pattern-match both outermost Sucs
           together; match comp_ev's Suc-Zero structure so OCaml derives fc and fab as
           snoc-with-dim_entry. *)
        match (c_witness, ab_witness) with
        | ( Suc (inner_c_ft, Dim_e (fmod_c, _, _), Tctxcat.Suc (Tctxcat.Zero, _)),
            Suc (inner_ab_ft, Dim_e (fmod_ab, _, _), Tctxcat.Suc (Tctxcat.Zero, _)) ) ->
            let Eq = Modality.src_uniq (F.dom fmod_c) (F.dom fmod_ab) in
            let Eq = Modality.tgt_uniq (F.dom fmod_c) (F.dom fmod_ab) in
            let Eq = F.uniq fmod_c fmod_ab in
            let new_inner = apply_perm mode_value inner_c_ft inner_ab_ft inner_perm in
            Insert (new_inner, Now))
    | Later inner_inner_ins -> (
        (* ab = (b', (y, k) dim_entry) snoc; inner_b = (a'_inner, (y, k) dim_entry) snoc.
           Peel the (y, k) dim_entry from ab_witness; construct inner_b's witness by
           combining a witness for a'_inner (= b' minus the (x, n) inserted at
           inner_inner_ins's position) with the (y, k) dim_entry on top.  Then recurse
           [apply_perm] on inner_perm and [apply_insert_walk] on inner_inner_ins. *)
        match ab_witness with
        | Suc (inner_ab_ft, Dim_e (fmod_yk, k_val, filt_yk), Tctxcat.Suc (Tctxcat.Zero, _)) -> (
            let b'_tctx = FT.dom inner_ab_ft in
            let a'_inner_tctx = insert_dom inner_inner_ins b'_tctx in
            let inner_b_tctx = Tctx.suc a'_inner_tctx (Dim (k_val, filt_yk)) in
            let (Exists inner_b_witness_raw) = FT.exists inner_b_tctx in
            (* Align inner_b_witness's Cod-source with the function's [fmode] (via fab from
                ab_witness destructure), and check target is unit. *)
            let inner_b_src =
              match FT.src inner_b_witness_raw with
              | Mode_obj f -> f
              | Unit_obj -> Mode.not_unit mode_value Eq in
            let ab_src =
              match FT.src ab_witness with
              | Mode_obj f -> f
              | Unit_obj -> Mode.not_unit mode_value Eq in
            let Eq = F.Obj.uniq inner_b_src ab_src in
            match FT.tgt inner_b_witness_raw with
            | Mode_obj ft -> Mode.not_unit (F.Obj.dom ft) Eq
            | Unit_obj -> (
                (* Destructure inner_b_witness_raw too, exposing the inner-of-inner_b
                     witness and the F-image of (y, k) dim_entry.  This lets OCaml see
                     finner_b as snoc-with-dim_entry. *)
                match inner_b_witness_raw with
                | Suc
                    (inner_b_inner_ft, Dim_e (fmod_yk_inner_b, _, _), Tctxcat.Suc (Tctxcat.Zero, _))
                  -> (
                    let Eq = Modality.src_uniq (F.dom fmod_yk) (F.dom fmod_yk_inner_b) in
                    let Eq = Modality.tgt_uniq (F.dom fmod_yk) (F.dom fmod_yk_inner_b) in
                    let Eq = F.uniq fmod_yk fmod_yk_inner_b in
                    match c_witness with
                    | Suc (inner_c_ft, Dim_e (fmod_xn, _, _), Tctxcat.Suc (Tctxcat.Zero, _)) ->
                        let new_inner_perm =
                          apply_perm mode_value inner_c_ft inner_b_witness_raw inner_perm in
                        (* Walk inner_inner_ins structurally to produce its F-image. *)
                        let new_inner_inner_ins =
                          apply_insert_walk inner_b_inner_ft inner_ab_ft fmod_xn inner_inner_ins
                        in
                        Insert (new_inner_perm, Later new_inner_inner_ins)))))

  (* Walk an [insert] (an [(a, x, n, b) insert]) along with witnesses for [a] and [b] and an
     F.t for [x], producing the F-image insert at [(fa, fx, n, fb) insert].  The structure
     mirrors insert's [Now]/[Later]; each [Later] step peels a "passing" dim_entry from both
     witnesses (same on both sides) and recurses.  At [Now], the inserted dim_entry is on top
     of [b]; we destructure b's witness to verify and return [Now]. *)
  and apply_insert_walk : type mode a x n b fmode fa fb x_dom x_mode fx_dom fx fx_mode.
      (mode, a, unit, fmode, fa, unit) FT.t ->
      (mode, b, unit, fmode, fb, unit) FT.t ->
      (x_dom, x, x_mode, fx_dom, fx, fx_mode) F.t ->
      (a, x, n, b) insert ->
      (fa, fx, n, fb) insert =
   fun a_witness b_witness fmod_xn ins ->
    match ins with
    | Now -> (
        (* b = (a, (x, n) dim_entry) snoc.  Destructure b_witness's outer Suc with Dim_e for
           (x, n) to expose the F-image structure. *)
        match b_witness with
        | Suc (b_inner_ft, Dim_e (fmod_xn_b, _, _), Tctxcat.Suc (Tctxcat.Zero, _)) ->
            let Eq = Modality.src_uniq (F.dom fmod_xn) (F.dom fmod_xn_b) in
            let Eq = Modality.tgt_uniq (F.dom fmod_xn) (F.dom fmod_xn_b) in
            let Eq = F.uniq fmod_xn fmod_xn_b in
            (* Align a_witness with b_inner_ft via FT.uniq (both for [a]). *)
            let Eq = FT.uniq a_witness b_inner_ft in
            Now)
    | Later inner -> (
        (* a = (a_inner, (y, k) dim_entry) snoc.  b = (b_inner, (y, k) dim_entry) snoc.
           Destructure both witnesses and recurse. *)
        match (a_witness, b_witness) with
        | ( Suc (a_inner_ft, Dim_e (fmod_yk_a, _, _), Tctxcat.Suc (Tctxcat.Zero, _)),
            Suc (b_inner_ft, Dim_e (fmod_yk_b, _, _), Tctxcat.Suc (Tctxcat.Zero, _)) ) ->
            let Eq = Modality.src_uniq (F.dom fmod_yk_a) (F.dom fmod_yk_b) in
            let Eq = Modality.tgt_uniq (F.dom fmod_yk_a) (F.dom fmod_yk_b) in
            let Eq = F.uniq fmod_yk_a fmod_yk_b in
            let new_inner = apply_insert_walk a_inner_ft b_inner_ft fmod_xn inner in
            Later new_inner)

  (* Walk a [Lock.t] (= F-image of one [perm.Lock]'s modality generator) in parallel with the
     two [Tctxcat.comp] evidences from [c_witness]'s and [ab_witness]'s outer [FT.Suc].  For
     each [Lock_lock] generator in the [Lock.t], add one [perm.Lock] wrapper around the inner
     permute.  At [Zero] (= F maps generator to identity), return the inner permute unwrapped. *)
  and wrap_perm_with_locks : type fdom fmodality fcod flocks fc_inner fab_inner fc fab.
      (fc_inner, fab_inner) permute ->
      (fdom, fmodality, fcod, fdom, flocks, fcod) Lock.t ->
      (fdom, flocks, fcod, fc_inner, unit, fc) Tctxcat.comp ->
      (fdom, flocks, fcod, fab_inner, unit, fab) Tctxcat.comp ->
      (fc, fab) permute =
   fun inner_perm lock_ev c_cev ab_cev ->
    match (lock_ev, c_cev, ab_cev) with
    | Zero _, Zero, Zero -> inner_perm
    | ( Suc (inner_lock_ev, Inject (Lock_lock _), Tctxcat.Suc (Tctxcat.Zero, Lock g_lock_sub)),
        Tctxcat.Suc (c_cev_inner, Lock g_c_outer),
        Tctxcat.Suc (ab_cev_inner, Lock g_ab_outer) ) ->
        let Eq = Modality.Gen.src_uniq g_c_outer g_lock_sub in
        let Eq = Modality.Gen.tgt_uniq g_c_outer g_lock_sub in
        let Eq = Modality.Gen.src_uniq g_ab_outer g_lock_sub in
        let Eq = Modality.Gen.tgt_uniq g_ab_outer g_lock_sub in
        Lock (wrap_perm_with_locks inner_perm inner_lock_ev c_cev_inner ab_cev_inner)

  (* Walk [perm.Lock inner_perm]: [c]'s top is a [lock_entry], [c_witness]'s top is a
     [Lock_e].  The F-image of the outer lock generator may be a multi-edge or zero-edge
     lock path (Lock-preserving F is a special case with one edge); we wrap [inner_perm]
     with one [perm.Lock] per F-image lock entry via [wrap_perm_with_locks]. *)
  and apply_perm_lock : type mode c' n_mod inner_b fmode fc fab.
      mode Mode.t ->
      (mode, (c', n_mod lock_entry) snoc, unit, fmode, fc, unit) FT.t ->
      (mode, (inner_b, n_mod lock_entry) snoc, unit, fmode, fab, unit) FT.t ->
      (c', inner_b) permute ->
      (fc, fab) permute =
   fun mode_value c_witness ab_witness inner_perm ->
    let _ = mode_value in
    match (c_witness, ab_witness) with
    | ( Suc (inner_c_ft, Lock_e (g_c, fmod_c, lock_ev_c), c_cev),
        Suc (inner_ab_ft, Lock_e (g_ab, fmod_ab, lock_ev_ab), ab_cev) ) ->
        (* Align c_witness and ab_witness existentials at the outer Lock entry. *)
        let Eq = Modality.Gen.src_uniq g_c g_ab in
        let Eq = Modality.Gen.tgt_uniq g_c g_ab in
        let Eq = F.uniq fmod_c fmod_ab in
        let Eq = Lock.uniq lock_ev_c lock_ev_ab in
        let inner_mode_value = Modality.Gen.tgt g_c in
        let new_inner_perm = apply_perm inner_mode_value inner_c_ft inner_ab_ft inner_perm in
        wrap_perm_with_locks new_inner_perm lock_ev_c c_cev ab_cev

  (* Parallel walk of [annotate] (VarAnnotate.fwd_t) and [comp] (Tctx.bcomp), both sharing
     the inner morph [b] (= a path of dim entries).  Each [Suc] step F-images one [(modality,
     n) dim_entry] edge, extending the outer witness via [extend_witness_dim].  At the [Zero]
     base case, [b = id] and the composite [ab = a], so the output witness is unchanged. *)
  and apply_annotate_bcomp : type n mode annotations b a ab fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (mode, fmode) F.Obj.t ->
      (n, mode, annotations, mode, mode, b, mode) VarAnnotate.fwd_t ->
      (mode, b, mode, a, unit, ab) Tctx.bcomp ->
      (n, mode, fmode, annotations, b, a, fa, ab) annotate_bcomp_image =
   fun witness fab ann bc ->
    match (ann, bc) with
    | Zero (VarAnnotator.Obj.Eq _), Zero ->
        let fmode_t = F.Obj.cod fab in
        Annotate_bcomp_image (Zero (VarAnnotator.Obj.Eq fmode_t), Zero, witness)
    | Suc (VarAnnotator.Annotate filt, inner_ann), Suc (Dim (n_val, _), inner_bc) ->
        let modality = Modality.filter_modality filt in
        let (Exists fmod) = F.exists modality in
        let witness_tgt = F.tgt fmod in
        let Eq = F.Obj.uniq witness_tgt fab in
        let new_filt = FFilter.apply fmod filt in
        let ext_witness = extend_witness_dim witness fmod n_val (Modality.filter_idempotent filt) in
        let (Annotate_bcomp_image (new_inner_ann, new_inner_bc, final_witness)) =
          apply_annotate_bcomp ext_witness fab inner_ann inner_bc in
        Annotate_bcomp_image
          ( Suc (VarAnnotator.Annotate new_filt, new_inner_ann),
            Suc (Dim (n_val, Modality.filter_idempotent new_filt), new_inner_bc),
            final_witness )

  (* Walk a [VarAnnotate.fwd_t] (the variable-annotation chain in a branch) and apply F to
     each annotation's modality.  The fwd_t is cons-based: each [Suc] gives the outer/source-
     side edge (a [VarAnnotator.Annotate modality]) followed by the inner rest.  Both ends of
     the chain are at [mode] (VarAnnote is endo); we thread an [F.Obj.t] witness from [mode]
     to [fmode] throughout. *)
  and apply_var_annotate_fwd : type n mode annotations b fmode.
      (mode, fmode) F.Obj.t ->
      (n, mode, annotations, mode, mode, b, mode) VarAnnotate.fwd_t ->
      (mode, fmode, n, annotations, b) annotate_fwd_image =
   fun fab fwd ->
    match fwd with
    | Zero _ ->
        let fmode_t = F.Obj.cod fab in
        Annotate_fwd_image (Zero (VarAnnotator.Obj.Eq fmode_t))
    | Suc (VarAnnotator.Annotate filt, inner_fwd) ->
        let modality = Modality.filter_modality filt in
        let (Exists fmod) = F.exists modality in
        let witness_tgt = F.tgt fmod in
        let Eq = F.Obj.uniq witness_tgt fab in
        let (Annotate_fwd_image new_inner) = apply_var_annotate_fwd fab inner_fwd in
        Annotate_fwd_image (Suc (VarAnnotator.Annotate (FFilter.apply fmod filt), new_inner))

  and apply_structfield : type i mode n a s et fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (i, mode * (n * a * s * et)) Term.Structfield.t ->
      (i, fmode * (n * fa * s * et)) Term.Structfield.t =
   fun witness sf ->
    match sf with
    | Lower (adj, plus_lock_ev, tm, label) ->
        let (Adjunction_image (_, fmod_right, new_adj)) = apply_adjunction adj in
        let (Plus_lock_image (fmod_pl, new_plus_lock, new_witness)) =
          apply_plus_lock witness plus_lock_ev in
        let Eq = Modality.src_uniq (F.dom fmod_right) (F.dom fmod_pl) in
        let Eq = F.uniq fmod_right fmod_pl in
        let new_tm = apply_term new_witness tm in
        Lower (new_adj, new_plus_lock, new_tm, label)
    | Higher (adj, plus_lock_ev, ppbm) ->
        let (Adjunction_image (_, fmod_right, new_adj)) = apply_adjunction adj in
        let (Plus_lock_image (fmod_pl, new_plus_lock, new_witness)) =
          apply_plus_lock witness plus_lock_ev in
        let Eq = Modality.src_uniq (F.dom fmod_right) (F.dom fmod_pl) in
        let Eq = F.uniq fmod_right fmod_pl in
        Higher (new_adj, new_plus_lock, apply_plus_pbijmap new_witness ppbm)
    | LazyHigher (adj, plus_lock_ev, ppbm) ->
        let (Adjunction_image (_, fmod_right, new_adj)) = apply_adjunction adj in
        let (Plus_lock_image (fmod_pl, new_plus_lock, new_witness)) =
          apply_plus_lock witness plus_lock_ev in
        let Eq = Modality.src_uniq (F.dom fmod_right) (F.dom fmod_pl) in
        let Eq = F.uniq fmod_right fmod_pl in
        LazyHigher (new_adj, new_plus_lock, lazy (apply_plus_pbijmap new_witness (Lazy.force ppbm)))

  (* Apply F to a PlusPbijmap (= Pbijmap of PlusFam.t). *)
  and apply_plus_pbijmap : type n i mode a fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (n, i, mode * a) Term.PlusPbijmap.t ->
      (n, i, fmode * fa) Term.PlusPbijmap.t =
   fun witness ppbm ->
    Term.PlusPbijmap.mmap
      {
        map =
          (fun pbij [ opt_pf ] ->
            match opt_pf with
            | None -> None
            | Some
                (Term.PlusFam.PlusFam
                   (type rb)
                   ((plusmap, body) :
                     (_, a, rb, mode) plusmap * (mode, rb, Energy.potential) Term.term)) -> (
                let r = Dim.remaining pbij in
                let rb_tctx = Plusmap.cod r plusmap in
                let (Exists ft_rb) = FT.exists rb_tctx in
                let Eq = EntryMap.Obj.uniq (FT.src witness) (FT.src ft_rb) in
                match FT.tgt ft_rb with
                | Mode_obj fab -> Mode.not_unit (F.Obj.dom fab) Eq
                | Unit_obj ->
                    let new_body = apply_term ft_rb body in
                    let new_plusmap_raw = plusmap_commute r witness plusmap ft_rb in
                    let (Anyplus.Obj.Eq _) = Plusmap.src new_plusmap_raw in
                    let (Anyplus.Obj.Eq _) = Plusmap.tgt new_plusmap_raw in
                    Some
                      (Term.PlusFam.PlusFam
                         ( (new_plusmap_raw : (_, fa, _, fmode) plusmap),
                           (new_body : (fmode, _, _) Term.term) ))));
      }
      [ ppbm ]

  and apply_struct_args : type mode n a s et fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (mode, n, a, s, et) Term.struct_args ->
      (fmode, n, fa, s, et) Term.struct_args =
   fun witness { dim; fields; eta; energy } ->
    let new_fields =
      Bwd.Bwd.map
        (fun (Term.StructfieldAbwd.Entry (key, sf)) ->
          Term.StructfieldAbwd.Entry (key, apply_structfield witness sf))
        fields in
    { dim; fields = new_fields; eta; energy }

  and apply_canonical : type mode a fmode fa.
      (mode, a, fmode, fa) tctx_fmap -> (mode, a) Term.canonical -> (fmode, fa) Term.canonical =
   fun witness c ->
    match c with
    | Data { indices; constrs; discrete; recursive; hints } ->
        let new_constrs = Bwd.Bwd.map (fun (k, dc) -> (k, apply_dataconstr witness dc)) constrs in
        Data { indices; constrs = new_constrs; discrete; recursive; hints }
    | Codata cargs ->
        let (Codata_args_image new_cargs) = apply_codata_args witness cargs in
        Codata new_cargs

  and apply_binding : type mode a fmode fa.
      (mode, a, fmode, fa) tctx_fmap -> (mode, a) Term.binding -> (fmode, fa) Term.binding =
   fun witness { ty; tm } -> { ty = apply_term witness ty; tm = Option.map (apply_term witness) tm }

  and apply_codatafield : type i mode a n et fmode fa.
      mode Mode.t ->
      (mode, a, fmode, fa) tctx_fmap ->
      n D.t ->
      i D.t ->
      (i, mode * a * n * et) Term.Codatafield.t ->
      (i, fmode * fa * n * et) Term.Codatafield.t =
   fun mode_value witness n i cf ->
    match cf with
    | Lower (adj, plus_lock_ev, tm) ->
        let fab =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit mode_value Eq in
        let id_fmod = F.id fab in
        let ext_witness = extend_witness_dim witness id_fmod n (Modality.filter_id mode_value n) in
        let (Adjunction_image (_, fmod_right, new_adj)) = apply_adjunction adj in
        let (Plus_lock_image (fmod_pl, new_plus_lock, new_witness)) =
          apply_plus_lock ext_witness plus_lock_ev in
        let Eq = Modality.src_uniq (F.dom fmod_right) (F.dom fmod_pl) in
        let Eq = F.uniq fmod_right fmod_pl in
        let new_tm = apply_term new_witness tm in
        ignore i;
        Lower (new_adj, new_plus_lock, new_tm)
    | Higher (adj, plusmap, plus_lock_ev, body) -> (
        (* Higher's plusmap: ('i, (a, (mode id, D.zero) dim_entry) snoc, ian, mode) plusmap.
           The body lives at [ian] locked by the right adjoint of [adj].  We extend the witness
           by [(mode id, D.zero) dim_entry], use [FT.exists ian_tctx] for the F-image witness of
           [ian], then apply F to the adjunction and the plus_lock, threading the resulting
           witness to the body. *)
        let fab =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit mode_value Eq in
        let id_fmod = F.id fab in
        let ext_witness =
          extend_witness_dim witness id_fmod D.zero (Modality.filter_id mode_value D.zero) in
        let ian_tctx = Plusmap.cod i plusmap in
        let (Exists ft_ian) = FT.exists ian_tctx in
        match FT.tgt ft_ian with
        | Mode_obj fab_tgt -> Mode.not_unit (F.Obj.dom fab_tgt) Eq
        | Unit_obj ->
            let ft_ian_src =
              match FT.src ft_ian with
              | Mode_obj f -> f
              | Unit_obj -> Mode.not_unit mode_value Eq in
            let Eq = F.Obj.uniq ft_ian_src fab in
            let new_plusmap = plusmap_commute i ext_witness plusmap ft_ian in
            let (Adjunction_image (_, fmod_right, new_adj)) = apply_adjunction adj in
            let (Plus_lock_image (fmod_pl, new_plus_lock, new_witness)) =
              apply_plus_lock ft_ian plus_lock_ev in
            let Eq = Modality.src_uniq (F.dom fmod_right) (F.dom fmod_pl) in
            let Eq = F.uniq fmod_right fmod_pl in
            let new_body = apply_term new_witness body in
            Higher (new_adj, new_plusmap, new_plus_lock, new_body))

  and apply_codata_fibrancy : type mode g n nh b hb et fmode fb.
      mode Mode.t ->
      (mode, b, fmode, fb) tctx_fmap ->
      (mode, g, n, nh, b, hb, et) Term.codata_fibrancy ->
      (mode, g, n, nh, b, hb, et, fmode, fb) codata_fibrancy_image =
   fun mode_value witness fib ->
    let { Term.glue; dim; length; plusmap; eta; ty; dimh; trr; trl; liftr; liftl } = fib in
    ignore length;
    let new_ty = apply_term witness ty in
    let fab =
      match FT.src witness with
      | Mode_obj f -> f
      | Unit_obj -> Mode.not_unit mode_value Eq in
    let new_length : (fmode, fb) Tctx.t = FT.cod witness in
    let hb_tctx = Plusmap.cod Hott.dim plusmap in
    let (Exists ft_hb) = FT.exists hb_tctx in
    match FT.tgt ft_hb with
    | Mode_obj fab_tgt -> Mode.not_unit (F.Obj.dom fab_tgt) Eq
    | Unit_obj ->
        let ft_hb_src =
          match FT.src ft_hb with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit mode_value Eq in
        let Eq = F.Obj.uniq ft_hb_src fab in
        let new_plusmap = plusmap_commute Hott.dim witness plusmap ft_hb in
        let id_fmod = F.id fab in
        let ext_hb_witness =
          extend_witness_dim ft_hb id_fmod D.zero (Modality.filter_id mode_value D.zero) in
        let map_sf_abwd abwd =
          Bwd.Bwd.map
            (fun (Term.StructfieldAbwd.Entry (key, sf)) ->
              Term.StructfieldAbwd.Entry (key, apply_structfield ext_hb_witness sf))
            abwd in
        Codata_fibrancy_image
          {
            glue;
            dim;
            length = new_length;
            plusmap = new_plusmap;
            eta;
            ty = new_ty;
            dimh;
            trr = map_sf_abwd trr;
            trl = map_sf_abwd trl;
            liftr = map_sf_abwd liftr;
            liftl = map_sf_abwd liftl;
          }

  and apply_is_glue : type mode n a et fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (mode, n, a, et) Term.is_glue ->
      (fmode, n, fa, et) Term.is_glue =
   fun witness g ->
    (* By pattern-matching the witness deeply and aligning each Dim_e's F.t with [F.id fab_proj]
       (since the Glue tctx's modalities are all [mode id]) plus the Proj_e's F.Obj.t, OCaml
       can derive that [fa] matches the specific F-image Glue tctx shape, allowing [Glue] to
       be constructed at the output type. *)
    match (witness, g) with
    | ( Suc
          ( Suc
              ( Suc
                  ( Suc
                      ( Suc (Zero _, Proj_e fab_proj, Tctxcat.Suc (Tctxcat.Zero, _)),
                        Dim_e (fmod1, _, _),
                        Tctxcat.Suc (Tctxcat.Zero, _) ),
                    Dim_e (fmod2, _, _),
                    Tctxcat.Suc (Tctxcat.Zero, _) ),
                Dim_e (fmod3, _, _),
                Tctxcat.Suc (Tctxcat.Zero, _) ),
            Dim_e (fmod4, _, _),
            Tctxcat.Suc (Tctxcat.Zero, _) ),
        Glue ) ->
        (* Each Dim_e's modality is [mode id] by the Glue tctx shape.  Destructuring
           [F.dom fmod_i] as [Path (Zero, _)] forces source = target at the modality level
           (since the id path's source and target coincide), aligning each F.t's Dom with
           [F.id fab_proj]'s Dom statically via GADT refinement. *)
        let (Path (Zero, _)) = F.dom fmod1 in
        let (Path (Zero, _)) = F.dom fmod2 in
        let (Path (Zero, _)) = F.dom fmod3 in
        let (Path (Zero, _)) = F.dom fmod4 in
        let id_fmod = F.id fab_proj in
        let Eq = F.uniq fmod1 id_fmod in
        let Eq = F.uniq fmod2 id_fmod in
        let Eq = F.uniq fmod3 id_fmod in
        let Eq = F.uniq fmod4 id_fmod in
        Term.Glue

  and apply_codata_args : type mode n c a nh ha et fmode fa.
      (mode, a, fmode, fa) tctx_fmap ->
      (mode, n, c, a, nh, ha, et) Term.codata_args ->
      (mode, n, c, a, nh, ha, et, fmode, fa) codata_args_image =
   fun witness cargs ->
    let { Term.eta; opacity; hints; dim; termctx; fields; fibrancy; is_glue } = cargs in
    let fab =
      match FT.src witness with
      | Mode_obj f -> f
      | Unit_obj -> fatal (Anomaly "apply_codata_args: no mode") in
    let mode_value = F.Obj.dom fab in
    let id_fmod = F.id fab in
    let ext_witness = extend_witness_dim witness id_fmod dim (Modality.filter_id mode_value dim) in
    let new_termctx = Option.map (apply_termctx ext_witness) termctx in
    let new_fields =
      Bwd.Bwd.map
        (fun (Term.CodatafieldAbwd.Entry (key, cf)) ->
          Term.CodatafieldAbwd.Entry
            (key, apply_codatafield mode_value witness dim (Field.dim key) cf))
        fields in
    let (Codata_fibrancy_image new_fibrancy) = apply_codata_fibrancy mode_value witness fibrancy in
    let new_is_glue = Option.map (apply_is_glue witness) is_glue in
    Codata_args_image
      {
        eta;
        opacity;
        hints;
        dim;
        termctx = new_termctx;
        fields = new_fields;
        fibrancy = new_fibrancy;
        is_glue = new_is_glue;
      }

  and apply_termctx : type mode a b fmode fb.
      (mode, b, fmode, fb) tctx_fmap -> (mode, a, b) Term.termctx -> (fmode, a, fb) Term.termctx =
   fun witness (Permute (perm, ord)) -> Permute (perm, apply_ordered_termctx witness ord)

  (* Walk a Lock.t evidence (= F-image of a single Modality generator) and wrap an inner
     ordered_termctx with one [Term.Lock] constructor per generator in the path.  When the
     Lock.t is Zero (F mapped the input generator to the identity modality), the inner
     ordered_termctx is returned unchanged (its mode equals the F-image dom).  The recursion
     processes the inner Lock.t first (going from the outer target down toward the inner
     source) and then wraps with the current edge's [Lock_lock] generator. *)
  and wrap_locks_around_ordered_termctx : type fdom fmodality fcod fa fb flocks_shape fb_locked.
      (fdom, fmodality, fcod, fdom, flocks_shape, fcod) Lock.t ->
      (fcod, fa, fb) Term.ordered_termctx ->
      (fdom, flocks_shape, fcod, fb, unit, fb_locked) Tctx.comp ->
      (fdom, fa, fb_locked) Term.ordered_termctx =
   fun lock_ev acc comp ->
    match (lock_ev, comp) with
    | Zero _, Zero -> acc
    | Suc (inner_lock_ev, Inject (Lock_lock g1), Suc (Zero, Lock _)), Suc (comp, Lock g3) ->
        let Eq = Modality.Gen.tgt_uniq g1 g3 in
        let acc_after_inner = wrap_locks_around_ordered_termctx inner_lock_ev acc comp in
        Term.Lock (acc_after_inner, g1)

  and apply_ordered_termctx : type mode a b fmode fb.
      (mode, b, fmode, fb) tctx_fmap ->
      (mode, a, b) Term.ordered_termctx ->
      (fmode, a, fb) Term.ordered_termctx =
   fun witness ord ->
    match ord with
    | Emp mode -> (
        (* Pattern-match the witness's specific structure for [mode emp] = single-Proj path
           so OCaml derives [fb] = [(unit id, fmode proj) snoc]. *)
        ignore mode;
        match witness with
        | Suc (Zero Unit_obj, Proj_e fab_proj, Tctxcat.Suc (Tctxcat.Zero, _)) ->
            let fmode_t = F.Obj.cod fab_proj in
            Term.Emp fmode_t
        | Suc (Zero (Mode_obj fab), _, _) -> Mode.not_unit (F.Obj.dom fab) Eq)
    | Ext (inner, entry, nplus) -> (
        (* The outer witness covers [(b, (modality, n) dim_entry) snoc].  Pattern-match Suc
           with a [Dim_e] edge (which has src = tgt = mode) to extract the inner-witness for
           [b], shared by [inner] and the entry. *)
        match witness with
        | Suc (inner_witness, Dim_e (witness_fmod, _, _), Tctxcat.Suc (Tctxcat.Zero, _)) -> (
            let new_inner = apply_ordered_termctx inner_witness inner in
            match apply_entry inner_witness entry with
            | Entry_image
                (type fdom_e fmodality_e fbm_e)
                ((entry_fmod, new_entry) :
                  (_, _, _, fdom_e, fmodality_e, _) F.t
                  * (fdom_e, fmodality_e, _, _, fbm_e, _, _) Term.entry) ->
                let Eq = Modality.src_uniq (F.dom entry_fmod) (F.dom witness_fmod) in
                let Eq = F.uniq entry_fmod witness_fmod in
                Term.Ext (new_inner, new_entry, nplus)))
    | Lock (inner, gen) ->
        (* F maps the single Modality.gen to a possibly-multi-edge modality path.  We apply F
           to [of_gen gen], walk the resulting Lock.t evidence, and fold each generator into
           a [Term.Lock] wrapper around the recursively-F-imaged [inner]. *)
        let (Suc (inner_witness, Lock_e (g_witness, _, flock_ev), fb_fg)) = witness in
        let Eq = Modality.Gen.tgt_uniq gen g_witness in
        let new_inner = apply_ordered_termctx inner_witness inner in
        let result = wrap_locks_around_ordered_termctx flock_ev new_inner fb_fg in
        result
    | Weaken (inner, code) ->
        (* A [Weaken] increments the raw length without changing the tctx shape [b], so the
           witness is unchanged. *)
        Weaken (apply_ordered_termctx witness inner, code)

  and apply_entry : type dom modality mode b bm x n fmode fb.
      (mode, b, fmode, fb) tctx_fmap ->
      (dom, modality, mode, b, bm, x, n) Term.entry ->
      (dom, modality, mode, b, bm, x, n, fmode, fb) entry_image =
   fun witness entry ->
    match entry with
    | Vis { dim; plus_lock; plusdim; filter; vars; bindings; hasfields; fields; fplus } ->
        let (Plus_lock (lock_ev, _)) = plus_lock in
        let modality = Lock.dom lock_ev in
        let (Exists fmod) = F.exists modality in
        let witness_src =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit (Modality.tgt modality) Eq in
        let Eq = F.Obj.uniq witness_src (F.tgt fmod) in
        let mn_dim = D.plus_out dim plusdim in
        let ext_witness = extend_witness_dim witness fmod mn_dim filter in
        let (Plus_lock_image (fmod_pl, new_plus_lock, bm_witness)) =
          apply_plus_lock ext_witness plus_lock in
        let Eq = F.uniq fmod_pl fmod in
        let new_bindings =
          Dim.CubeOf.mmap { map = (fun _ [ b ] -> apply_binding bm_witness b) } [ bindings ] in
        let new_fields = Bwv.map (fun (k, s, tm) -> (k, s, apply_term bm_witness tm)) fields in
        Entry_image
          ( fmod,
            Term.Vis
              {
                dim;
                plus_lock = new_plus_lock;
                plusdim;
                filter = FFilter.apply fmod filter;
                vars;
                bindings = new_bindings;
                hasfields;
                fields = new_fields;
                fplus;
              } )
    | Invis { plus_lock; filter; bindings; hints } ->
        let (Plus_lock (lock_ev, _)) = plus_lock in
        let modality = Lock.dom lock_ev in
        let (Exists fmod) = F.exists modality in
        let witness_src =
          match FT.src witness with
          | Mode_obj f -> f
          | Unit_obj -> Mode.not_unit (Modality.tgt modality) Eq in
        let Eq = F.Obj.uniq witness_src (F.tgt fmod) in
        let n_dim = Dim.CubeOf.dim bindings in
        let ext_witness = extend_witness_dim witness fmod n_dim filter in
        let (Plus_lock_image (fmod_pl, new_plus_lock, bm_witness)) =
          apply_plus_lock ext_witness plus_lock in
        let Eq = F.uniq fmod_pl fmod in
        let new_bindings =
          Dim.CubeOf.mmap { map = (fun _ [ b ] -> apply_binding bm_witness b) } [ bindings ] in
        Entry_image
          ( fmod,
            Term.Invis
              {
                plus_lock = new_plus_lock;
                filter = FFilter.apply fmod filter;
                bindings = new_bindings;
                hints;
              } )
end
