(* This module should not be opened, but used qualified *)

open Util
open Modal
open Tbwd
open Dim
open Dimbwd
open Reporter
open Term
open Value

(* To first approximation, a context is a list of variables, each of which has a value that is a normal form.  Often the "value" of a variable will just be ITSELF, represented by a De Bruijn LEVEL, together of course with its type.  This can then appear in the types of later variables.  In particular, the LENGTH of this context, which is its type parameter as a type-level nat, is the current De Bruijn LEVEL for new variables to be added.

   We can look up the INDEX of a TERM VARIABLE into this Bwv to get its type.  This operation is statically guaranteed to succeed, since all De Bruijn indices are intrinsically well-scoped.

   We can also look up the LEVEL of a VALUE VARIABLE to find its corresponding term-variable index (and we do this during readback).  However, this operation is not statically guaranteed to succeed.  Indeed, in some cases it we intend for it to fail, e.g. during an occurs-check.  To enable this operation, we separately store for each index variable its corresponding level, if any, in addition to its value.  (If it is let-bound to a value, then it has no associated level variable.) *)

(* To second approximation, a "context" is actually a WEAKENING SUBSTITUTION from one De Bruijn INDEX context to another.  The index variables that arise from parsing are counted based on the number of textually in-scope variables, but internally there may be variables other than these, for instance if a pattern binds some arguments implicitly.  Thus, an element of (a, b) Ctx.t is actually a length-b context in which only a of the variables are "visible".  We then use b for counting the next De Bruijn LEVEL to create, and for De Bruijn INDICES IN CHECKED TERMS, as well as for readback.  However, since the user can only refer to a of the variables, and the parser doesn't know about invisible variables (they are determined by semantic considerations, e.g. implicit arguments of constructors in match patterns), we use a for De Bruijn INDICES IN RAW TERMS.  This means the index of a variable can change when it is typechecked, but our intrinsically well-scoped indices manage this issue smoothly, ensuring that the correct kind of index is always used in the correct place. *)

(* To third approximation, a context is not a flat list of variables, but a list of "cubes" of variables.  Frequently when introducing variables, we introduce a whole cube of them (e.g. when abstracting into a higher-dimensional pi-type, or pattern-matching against a higher-dimensional datatype), and we avoid "linearizing" these variables as much as possible.  Thus, index variables are not just a (well-scoped) natural number, but are paired with a dimension and a strict face of that dimension, and variables are stored in cubes.

   More precisely, the RAW parameter 'a is a simple type-level natural number, since the parser can't tell what dimensions things have, and a raw index variable is paired with a face of an arbitrary dimension corresponding to how the user used it.  However, the CHECKED parameter 'b is actually a type-level list of dimensions (an "hctx"), and a checked index variable is paired with a face *of the corresponding dimension*.  For level variables we use a pair of integers: one for the position in the context, and the other that counts through the variables in each cube.  (Since levels are only ever compared for equality, the ordering of the latter numbers doesn't matter.) *)

(* To fourth approximation, a context (qua substitution) can also incorporate a permutation of the raw indices.  This is because the raw indices occur in the order that they are bound *textually*, whereas we require that the checked indices occur in a "logical" order so that the type and possible value of each variable involves only those appearing prior to it.  These can disconnect during a match, where the new variables bound as arguments of the matched constructor are last textually, but must be inserted earlier in the context to retain logical order.  We postpone this modification until later, first defining "Ordered" contexts and then adding the permutations. *)

(* The binding of each variable in a context is a "level option * normal".  But instead of exposing this literally as a product type, we use an abstract type with a constructor "Binding.make" and accessors "Binding.level" and "Binding.value".  The reason is that in the "bind_some" machinery below, we work with contexts where the binding of a variable is "known but not yet available" or "not yet computed".  So the internal implementation of Binding is actually a reference cell that usually stores a "Known" "level option * normal", but sometimes is Unknown or other times a Delayed "level option * normal". *)
module Binding : sig
  type 'mode t

  val make : level option -> 'mode normal -> 'mode t
  val level : 'mode t -> level option
  val value : 'mode t -> 'mode normal

  (* An unknown binding can be specified when we have its value. *)
  val unknown : unit -> 'mode t
  val specify : 'mode t -> level option -> 'mode normal -> unit

  (* A known but not-yet-available value is created by delaying it, and can be made available by forcing it. *)
  val delay : 'mode t -> 'mode t
  val force : 'mode t -> unit

  (* An error value raises an exception when accessed. *)
  val error : Reporter.Code.t -> 'mode t
end = struct
  type 'mode state =
    | Known of level option * 'mode normal
    | Unknown
    | Delayed of level option * 'mode normal
    | Error of Reporter.Code.t

  type 'mode t = 'mode state ref

  let make i x = ref (Known (i, x))

  let level b =
    match !b with
    | Known (i, _) -> i
    | Unknown | Delayed _ -> None
    | Error e -> fatal e

  let value b =
    match !b with
    | Known (_, x) -> x
    | Unknown | Delayed _ -> fatal (Anomaly "Undetermined context variable")
    | Error e -> fatal e

  let unknown () = ref Unknown
  let specify b i x = b := Known (i, x)
  let delay b = ref (Delayed (level b, value b))
  let error e = ref (Error e)

  let force b =
    match !b with
    | Known _ | Unknown -> ()
    | Delayed (i, x) -> b := Known (i, x)
    | Error e -> fatal e
end

(* Test whether all the variables in a cube of bindings are free (none are let-bound). *)
let all_free : type mode n. (n, mode Binding.t) CubeOf.t -> bool =
 fun b ->
  let open CubeOf.Monadic (Monad.Maybe) in
  Option.is_some (mmapM { map = (fun _ [ x ] -> Option.map (fun _ -> ()) (Binding.level x)) } [ b ])

(* A context is a list of "entries", which can be either visible or invisible in the raw world.  An (f,n) entry contains f raw variables and an n-dimensional cube of checked variables. *)
type (_, _, _, _, _) entry =
  (* Add a cube of internal variables that are visible to the parser as a list of cubes of variables, the list-of-cubes being obtained by decomposing the dimension as a sum.  Note that the division into a cube and non-cube part, and the sum of dimensions, are only relevant for looking up *raw* indices: they are invisible to the checked world, whose indices store the total face of mn. *)
  | Vis :
      ('dom, 'modality, 'mode, 'm, 'n, 'mn, 'f1, 'f2, 'f) vis_data
      -> ('dom, 'modality, 'mode, 'f, 'mn) entry
  (* Add a cube of internal variables that are not visible to the parser.  We also allow a vector of "field view" variables that look to the user like ordinary variables but actually expand *at typechecking time* to field projections of the top invisible variable. *)
  | Invis :
      ('dom, 'modality, 'mode) Modality.t * ('n, 'dom Binding.t) CubeOf.t
      -> ('dom, 'modality, 'mode, N.zero, 'n) entry

and ('dom, 'modality, 'mode, 'm, 'n, 'mn, 'f1, 'f2, 'f) vis_data = {
  dim : 'm D.t;
  modality : ('dom, 'modality, 'mode) Modality.t;
  plusdim : ('m, 'n, 'mn) D.plus;
  (* We use an indexed cube to automatically count how many raw variables appear, by starting with zero and incrementing it for each entry in the cube.  It's tempting to want to start instead from the previous raw length of the context, thereby eliminating the "plus" parameter of Snoc, below; but this causes problems with telescopes (forwards contexts), below, whose raw indices are forwards natural numbers instead. *)
  vars : (N.zero, 'n, string option, 'f1) NICubeOf.t;
  bindings : ('mn, 'dom Binding.t) CubeOf.t;
  (* While typechecking a record, we expose the "self" variable as a list of "illusory" variables, visible only to raw terms, that are substituted at typechecking time with the fields of self. *)
  hasfields : ('m, 'f2) has_fields;
  fields : (D.zero Field.t * string, 'f2) Bwv.t;
  fplus : ('f1, 'f2, 'f) N.plus;
}

let raw_entry : type dom modality mode f n. (dom, modality, mode, f, n) entry -> f N.t = function
  | Vis { vars; fplus; _ } -> N.plus_out (NICubeOf.out N.zero vars) fplus
  | Invis _ -> N.zero

let dim_entry : type dom modality mode f n. (dom, modality, mode, f, n) entry -> n D.t = function
  | Vis { bindings; _ } | Invis (_, bindings) -> CubeOf.dim bindings

(* Given an entry containing no let-bound variables, produce an "app" that says how to apply a function to its cube of (free) variables. *)
let app_entry : type dom modality mode f n any.
    (mode, any) apps -> (dom, modality, mode, f, n) entry -> (mode, noninst) apps =
 fun apps e ->
  match e with
  | Vis { bindings; modality; _ } | Invis (modality, bindings) ->
      if all_free bindings then
        let n = CubeOf.dim bindings in
        Arg
          ( apps,
            modality,
            CubeOf.mmap { map = (fun _ [ x ] -> Binding.value x) } [ bindings ],
            ins_zero n )
      else fatal (Anomaly "let-bound variable in Ctx.apps")

module Ordered = struct
  type ('mode, _, _) t =
    | Emp : 'mode Mode.t -> ('mode, N.zero, emp) t
    | Snoc :
        ('mode, 'a, 'b) t * ('dom, 'modality, 'mode, 'x, 'n) entry * ('a, 'x, 'ax) N.plus
        -> ('mode, 'ax, ('b, 'n) snoc) t
    (* Modal locks change the mode of the context, but are NOT recorded in either length.  This is intentional because it allows multiple locks to be combined, or identity locks removed or treated as inserted without being mentioned, without needing to frobnicate the type parameters.  (Another approach would be to make the length record exactly one lock in between every pair of variables.) *)
    | Lock : ('cod, 'a, 'b) t * ('dom, 'modality, 'cod) Modality.t * bool -> ('dom, 'a, 'b) t

  let rec mode : type mode a b. (mode, a, b) t -> mode Mode.t = function
    | Emp mode -> mode
    | Snoc (ctx, Vis _, _) -> mode ctx
    | Snoc (ctx, Invis _, _) -> mode ctx
    | Lock (_, modality, _) -> Modality.dom modality

  let vis : type dom modality mode a b f af m n mn.
      (mode, a, b) t ->
      (dom, modality, mode) Modality.t ->
      m D.t ->
      (m, n, mn) D.plus ->
      (N.zero, n, string option, f) NICubeOf.t ->
      (mn, dom Binding.t) CubeOf.t ->
      (a, f, af) N.plus ->
      (mode, af, (b, mn) snoc) t =
   fun ctx modality dim plusdim vars bindings af ->
    Snoc
      ( ctx,
        Vis
          {
            dim;
            modality;
            plusdim;
            vars;
            bindings;
            hasfields = No_fields;
            fields = Emp;
            fplus = Zero;
          },
        af )

  let cube_vis : type dom modality mode a b n.
      (mode, a, b) t ->
      (dom, modality, mode) Modality.t ->
      string option ->
      (n, dom Binding.t) CubeOf.t ->
      (mode, a N.suc, (b, n) snoc) t =
   fun ctx modality x vars ->
    let m = CubeOf.dim vars in
    vis ctx modality m (D.plus_zero m) (NICubeOf.singleton x) vars (Suc Zero)

  let vis_fields : type mode a b f1 f2 f af n.
      (mode, a, b) t ->
      (N.zero, n, string option, f1) NICubeOf.t ->
      (n, mode Binding.t) CubeOf.t ->
      (D.zero Field.t * string, f2) Bwv.t ->
      (f1, f2, f) N.plus ->
      (a, f, af) N.plus ->
      (mode, af, (b, n) snoc) t =
   fun ctx vars bindings fields fplus af ->
    let plusdim = D.zero_plus (CubeOf.dim bindings) in
    let modality = Modality.id (mode ctx) in
    Snoc
      ( ctx,
        Vis
          { dim = D.zero; modality; plusdim; vars; bindings; hasfields = Has_fields; fields; fplus },
        af )

  let invis : type dom modality mode a b n.
      (mode, a, b) t ->
      (dom, modality, mode) Modality.t ->
      (n, dom Binding.t) CubeOf.t ->
      (mode, a, (b, n) snoc) t =
   fun ctx modality bindings -> Snoc (ctx, Invis (modality, bindings), Zero)

  (* Smart constructor that collapses multiple subsequent locks and omits identity locks. *)
  let rec lock : type dom modality cod a b.
      (cod, a, b) t -> ?parametric:bool -> (dom, modality, cod) Modality.t -> (dom, a, b) t =
   fun ctx ?(parametric = false) mu ->
    match ctx with
    | Lock (ctx, nu, was_parametric) ->
        let (Composed (numu, _)) = Modality.comp nu mu in
        let parametric = parametric || was_parametric in
        lock ctx ~parametric numu
    | _ -> (
        match (Modality.compare_id mu, parametric) with
        | Eq, false -> ctx
        | _ -> Lock (ctx, mu, parametric))

  let rec locked : type mode a b. (mode, a, b) t -> bool = function
    | Emp _ -> false
    | Snoc (ctx, _, _) -> locked ctx
    | Lock (_, _, true) -> true
    | Lock (ctx, _, false) -> locked ctx

  let rec checked_length : type mode a b. (mode, a, b) t -> b Tbwd.t = function
    | Emp _ -> Emp
    | Snoc (ctx, _, _) -> Snoc (checked_length ctx)
    | Lock (ctx, _, _) -> checked_length ctx

  let rec raw_length : type mode a b. (mode, a, b) t -> a N.t = function
    | Emp _ -> N.zero
    | Snoc (ctx, _, ax) -> N.plus_out (raw_length ctx) ax
    | Lock (ctx, _, _) -> raw_length ctx

  let rec length : type mode a b. (mode, a, b) t -> int = function
    | Emp _ -> 0
    | Snoc (ctx, _, _) -> length ctx + 1
    | Lock (ctx, _, _) -> length ctx

  let empty mode : ('mode, N.zero, emp) t = Emp mode

  let rec dbwd : type mode a b. (mode, a, b) t -> b Dbwd.t = function
    | Emp _ -> Word Zero
    | Snoc (ctx, e, _) ->
        let (Word b) = dbwd ctx in
        Word (Suc (b, dim_entry e))
    | Lock (ctx, _, _) -> dbwd ctx

  let rec apps : type mode a b. (mode, a, b) t -> (mode, noninst) apps = function
    | Emp _ -> Emp
    | Snoc (ctx, e, _) -> app_entry (apps ctx) e
    | Lock (_, _, _) -> fatal (Anomaly "context lock in Ctx.apps")

  (* When looking up a raw variable, we return either an ordinary value variable or an illusory field-access variable.  We also return the modality that annotates that entry, and the accumulated locks to its right. *)
  type (_, _) lookup =
    | Var : {
        level : level option;
        modality : ('dom, 'modality, 'cod) Modality.t;
        value : 'dom normal;
        index : 'b index;
        lock : ('mode, 'lock, 'cod) Modality.t;
      }
        -> ('mode, 'b) lookup
    | Field : {
        level : level;
        modality : ('dom, 'modality, 'cod) Modality.t;
        value : 'dom normal;
        field : D.zero Field.t;
        lock : ('mode, 'lock, 'cod) Modality.t;
      }
        -> ('mode, 'b) lookup

  (* The lookup function iterates through entries. *)
  let rec lookup : type mode a b. (mode, a, b) t -> a Raw.index -> (mode, b) lookup =
   fun ctx k ->
    match (ctx, k) with
    | Emp _, _ -> .
    | Snoc (ctx, e, pf), _ -> lookup_entry ctx e pf k
    | Lock (_, _, true), _ -> fatal Locked_variable
    | Lock (ctx, lock, false), _ -> (
        match lookup ctx k with
        | Var var ->
            let (Composed (lock, _)) = Modality.comp var.lock lock in
            Var { var with lock }
        | Field fld ->
            let (Composed (lock, _)) = Modality.comp fld.lock lock in
            Field { fld with lock })

  (* For each entry, we iterate through the list of fields or the cube of names, as appropriate. *)
  and lookup_entry : type dom modality mode a b f af mn.
      (mode, a, b) t ->
      (dom, modality, mode, f, mn) entry ->
      (a, f, af) N.plus ->
      af Raw.index ->
      (mode, (b, mn) snoc) lookup =
   fun ctx e pf k ->
    let pop = function
      | Var ({ index = Index (v, fa); _ } as var) -> Var { var with index = Index (Later v, fa) }
      | Field f -> Field f in
    let lock = Modality.id (mode ctx) in
    match e with
    | Vis
        (type m n f1 f2)
        ({ dim; modality; plusdim; vars; bindings; hasfields = _; fields; fplus } :
          (dom, modality, mode, m, n, mn, f1, f2, f) vis_data) -> (
        let (Plus pf1) = N.plus (NICubeOf.out N.zero vars) in
        let pf12 = N.plus_assocl pf1 fplus pf in
        match N.index_in_plus pf12 (fst k) with
        | Right i -> (
            let b = CubeOf.find_top bindings in
            match Binding.level b with
            | Some level ->
                Field
                  { level; modality; value = Binding.value b; field = fst (Bwv.nth i fields); lock }
            | None -> fatal (Anomaly "missing level in field view"))
        | Left i -> (
            let module Lookup = struct
              (* When we look up a visible variable in a context, we find the level (if any), the value, and the corresponding possibly-invisible variable.  To do this we have to iterate through each cube of variables from right-to-left as we decrement the raw index looking for the corresponding face.  So we need an auxiliary type family to keep track of where we are in that iteration and what result type we're expecting. *)
              type 'right t =
                | Unfound : (a, 'right, 'rest) N.plus * 'rest N.index -> 'right t
                | Found : ('l, n) sface -> 'right t
            end in
            let module Fold = NICubeOf.Traverse (Lookup) in
            (* This function is called on every step of that iteration through a cube.  It appears that we have to define it with an explicit type signature in order for it to end up sufficiently polymorphic. *)
            let lookup_folder : type left l.
                (l, n) sface ->
                (left, l, string option) NFamOf.t ->
                left N.suc Lookup.t ->
                left Lookup.t * (left, l, unit) NFamOf.t =
             fun fb (NFamOf _) acc ->
              match acc with
              | Found fa -> (Found fa, NFamOf ())
              | Unfound (Suc p, Pop k) -> (Unfound (p, k), NFamOf ())
              | Unfound (_, Top) -> (Found fb, NFamOf ()) in
            match
              Fold.fold_map_right { foldmap = (fun fb -> lookup_folder fb) } vars (Unfound (pf1, i))
            with
            | Unfound (Zero, j), _ -> pop (lookup ctx (j, snd k))
            | Found fb, _ ->
                (* Once we find the face in the cube of visible variables, we add it to the face specified by the user for a cube variable, if any, and look up the corresponding binding. *)
                let (SFace_of fa) =
                  match snd k with
                  | None -> SFace_of (id_sface dim)
                  | Some (Any_sface fa) -> (
                      match D.compare (cod_sface fa) dim with
                      | Neq -> fatal (Invalid_variable_face (dim, fa))
                      | Eq -> SFace_of fa) in
                let (Plus kl) = D.plus (dom_sface fb) in
                let fab = sface_plus_sface fa plusdim kl fb in
                let x = CubeOf.find bindings fab in
                Var
                  {
                    level = Binding.level x;
                    modality;
                    value = Binding.value x;
                    index = Index (Now, fab);
                    lock;
                  }))
    | Invis _ ->
        let Zero = pf in
        pop (lookup ctx k)

  (* Look up a De Bruijn level in a context and find the corresponding possibly-invisible index, if one exists. *)
  let rec find_level : type mode a b. (mode, a, b) t -> level -> b index option =
   fun ctx i ->
    match ctx with
    | Emp _ -> None
    | Snoc (ctx, Vis { bindings; _ }, _) -> find_level_in_cube ctx bindings i
    | Snoc (ctx, Invis (_, bindings), _) -> find_level_in_cube ctx bindings i
    | Lock (ctx, _, _) -> find_level ctx i

  and find_level_in_cube : type dom mode a b n.
      (mode, a, b) t -> (n, dom Binding.t) CubeOf.t -> level -> (b, n) snoc index option =
   fun ctx vars i ->
    let open CubeOf.Monadic (Monad.State (struct
      type t = (b, n) snoc index option
    end))
    in
    match
      miterM
        {
          it =
            (fun fa [ x ] s ->
              if Binding.level x = Some i then ((), Some (Index (Now, fa))) else ((), s));
        }
        [ vars ] None
    with
    | (), Some v -> Some v
    | (), None -> Option.map (fun (Index (v, fa)) -> Index (Later v, fa)) (find_level ctx i)

  (* Every context has an underlying environment that substitutes each (level) variable for itself (index).  This environment ALWAYS HAS DIMENSION ZERO, and therefore in particular the variables don't need to come with any boundaries. *)

  let env_entry : type mode n.
      (n, mode Binding.t) CubeOf.t -> (n, (mode, kinetic) lazy_eval) CubeOf.t =
   fun v ->
    CubeOf.mmap
      (* We defer the value because it might be Unknown or Delayed, but we don't want an error reported unless such a value is actually *used*. *)
      { map = (fun _ [ x ] -> defer (fun () -> Val (Binding.value x).tm)) }
      [ v ]

  (* This function traverses the entire context and computes the corresponding environment.  However, when we add permutations to environments below, we will also store a precomputed environment, so this function only needs to be called when the context has been globally modified. *)
  let rec env : type mode a b. (mode, a, b) t -> (mode, D.zero, b) env = function
    | Emp mode -> Emp (mode, D.zero)
    | Snoc (ctx, Vis { bindings; modality; _ }, _) ->
        LazyExt (env ctx, D.zero_plus (CubeOf.dim bindings), modality, env_entry bindings)
    | Snoc (ctx, Invis (modality, bindings), _) ->
        LazyExt (env ctx, D.zero_plus (CubeOf.dim bindings), modality, env_entry bindings)
    | Lock (ctx, lock, _) -> Key (env ctx, Modalcell.id lock)

  (* Extend a context by one new variable, without a value but with an assigned type. *)
  let ext : type dom modality mode a b.
      (mode, a, b) t ->
      (dom, modality, mode) Modality.t ->
      string option ->
      (dom, kinetic) value ->
      (mode, a N.suc, (b, D.zero) snoc) t * dom Binding.t =
   fun ctx modality x ty ->
    let n = length ctx in
    let b = Binding.make (Some (n, 0)) { tm = var modality (n, 0) ty; ty } in
    (cube_vis ctx modality x (CubeOf.singleton b), b)

  (* Extend a context by one new variable with an assigned value. *)
  let ext_let : type dom modality mode a b.
      (mode, a, b) t ->
      (dom, modality, mode) Modality.t ->
      string option ->
      dom normal ->
      (mode, a N.suc, (b, D.zero) snoc) t * dom Binding.t =
   fun ctx modality x v ->
    let b = Binding.make None v in
    (cube_vis ctx modality x (CubeOf.singleton b), b)

  (* Remove the last entry in a context.  Only works if that last entry is a fully-cube variable with no fields. *)
  type ('mode, _, _) pop =
    | Pop :
        ('mode, 'a, 'b) t * ('a N.suc, 'asuc) Eq.t * (('b, 'n) snoc, 'bn) Eq.t
        -> ('mode, 'asuc, 'bn) pop

  let pop : type mode a b. (mode, a, b) t -> (mode, a, b) pop option = function
    | Snoc (ctx, _, Suc Zero) -> Some (Pop (ctx, Eq, Eq))
    | _ -> None

  (* Generate a case tree consisting of a sequence of abstractions corresponding to the (checked) variables in a context.  The context must contain NO LET-BOUND VARIABLES, including field-access variables, since abstracting over them would not be well-defined.  (In general, we couldn't just omit them, because some of the variables in a cube could be bound but not others, and cubes in the context yield cube abstractions.  However, at least when this comment was written, this function was only used for contexts consisting entirely of 0-dimensional cubes without let-bound variables.)  Likewise it must contain NO MODAL LOCKS. *)
  let rec lam : type mode a b.
      (mode, a, b) t -> (mode, b, potential) term -> (mode, emp, potential) term =
   fun ctx tree ->
    match ctx with
    | Emp _ -> tree
    | Lock (_, _, _) -> fatal (Anomaly "context lock in Ctx.lam")
    | Snoc (ctx, Vis { dim; plusdim; vars; bindings; fplus = Zero; _ }, _) when all_free bindings ->
        lam ctx (Lam (Variables (dim, plusdim, vars), tree))
    | Snoc (ctx, Invis (_, bindings), _) when all_free bindings ->
        lam ctx (Lam (singleton_variables (CubeOf.dim bindings) None, tree))
    | _ -> fatal (Anomaly "let-bound variable in Ctx.lam")

  (* Delete some level variables from a context by making their bindings into "unknown".  This will cause readback to raise No_such_level if it encounters one of those variables, which can then be trapped as an occurs-check. *)
  let rec forget_levels : type mode a b. (mode, a, b) t -> (level -> bool) -> (mode, a, b) t =
   fun ctx forget ->
    let forget_bindings : type mode n. (n, mode Binding.t) CubeOf.t -> (n, mode Binding.t) CubeOf.t
        =
     fun bindings ->
      CubeOf.mmap
        {
          map =
            (fun _ [ b ] ->
              match Binding.level b with
              | Some x when forget x -> Binding.unknown ()
              | _ -> b);
        }
        [ bindings ] in
    match ctx with
    | Emp mode -> Emp mode
    | Lock (ctx, lock, parametric) -> Lock (forget_levels ctx forget, lock, parametric)
    | Snoc (ctx, Vis ({ bindings; _ } as e), af) ->
        Snoc (ctx, Vis { e with bindings = forget_bindings bindings }, af)
    | Snoc (ctx, Invis (mode, bindings), af) ->
        Snoc (ctx, Invis (mode, forget_bindings bindings), af)

  (* Peel off enough locks to make up a supplied modality, along with any entries between them. *)

  type (_, _) remove_lock =
    | Remove_lock : ('cod, 'a, 'b) t * ('b, 'c, 'bc) Tbwd.append -> ('cod, 'bc) remove_lock

  let remove_lock : type mode modality cod a bc.
      (mode, a, bc) t -> (mode, modality, cod) Modality.t -> (cod, bc) remove_lock =
   fun ctx modality ->
    let rec go : type mode modality cod a b c bc.
        (mode, a, b) t ->
        (mode, modality, cod) Modality.t ->
        (b, c, bc) Tbwd.append ->
        (cod, bc) remove_lock =
     fun ctx modality bc ->
      match Modality.compare_id modality with
      | Eq -> Remove_lock (ctx, bc)
      | Neq -> (
          match ctx with
          | Emp _ -> fatal (Anomaly "empty context when trying to remove nonidentity lock")
          | Snoc (ctx, _, _) -> go ctx modality (Append_cons bc)
          | Lock (ctx, l, _) -> (
              match Modality.factor modality l with
              | Some (Factored (modality, _)) -> go ctx modality bc
              | None -> fatal (Anomaly "remove_lock: modalities don't factor"))) in
    go ctx modality Append_nil
end

(* Now we define contexts that add a permutation of the raw indices.  For efficiency reasons we also precompute its environment as the context is built and store it.  We also store the next De Bruijn level (cube only, not internal face level) that may be added to the context; in most cases this equals the length of the context, but during bind_some we work temporarily with rearranged contexts containing old De Bruijn levels so it may be greater than the length.  The permutation acts only on variables, not on locks; it should only permute variables with other variables that have NO LOCKS IN BETWEEN, but we don't enforce that statically.  In particular, therefore, the mode of the permuted context is the same as the mode of its ordered version. *)

type ('mode, 'a, 'b) t =
  | Permute : {
      perm : ('a, 'i) N.perm;
      env : ('mode, D.zero, 'b) env;
      level : int;
      ctx : ('mode, 'i, 'b) Ordered.t;
    }
      -> ('mode, 'a, 'b) t

(* Nearly all the operations on ordered contexts are lifted to either ignore the permutations or add identities on the right. *)

let vis (Permute { perm; env; level; ctx }) modality m mn xs vars af =
  let (Plus bf) = N.plus (N.plus_right af) in
  Permute
    {
      perm = N.perm_plus perm af bf;
      env = LazyExt (env, D.zero_plus (CubeOf.dim vars), modality, Ordered.env_entry vars);
      level = level + 1;
      ctx = Ordered.vis ctx modality m mn xs vars bf;
    }

type (_, _) any = Any_ctx : ('mode, 'a, 'b) t -> ('mode, 'b) any
type (_, _) moded = Moded_ctx : ('mode, 'a, 'b) t -> ('a, 'b) moded

let variables_vis : type dom modality mode a b mn.
    (mode, a, b) t ->
    (dom, modality, mode) Modality.t ->
    mn variables ->
    (mn, dom Binding.t) CubeOf.t ->
    (mode, (b, mn) snoc) any =
 fun ctx modality (Variables (m, mn, xs)) vars ->
  let (Plus af) = N.plus (NICubeOf.out N.zero xs) in
  Any_ctx (vis ctx modality m mn xs vars af)

let cube_vis ctx modality x vars =
  let m = CubeOf.dim vars in
  vis ctx modality m (D.plus_zero m) (NICubeOf.singleton x) vars (Suc Zero)

let vis_fields (Permute { perm; env; level; ctx }) xs vars fields fplus af =
  let (Plus bf) = N.plus (N.plus_right af) in
  let modality = Modality.id (Ordered.mode ctx) in
  Permute
    {
      perm = N.perm_plus perm af bf;
      env = LazyExt (env, D.zero_plus (CubeOf.dim vars), modality, Ordered.env_entry vars);
      level = level + 1;
      ctx = Ordered.vis_fields ctx xs vars fields fplus bf;
    }

let invis (Permute { perm; env; level; ctx }) modality vars =
  Permute
    {
      perm;
      env = LazyExt (env, D.zero_plus (CubeOf.dim vars), modality, Ordered.env_entry vars);
      level = level + 1;
      ctx = Ordered.invis ctx modality vars;
    }

let lock : type dom modality cod a b.
    (cod, a, b) t -> ?parametric:bool -> (dom, modality, cod) Modality.t -> (dom, a, b) t =
 fun (Permute { perm; env; level; ctx }) ?(parametric = false) lock ->
  let env = key_env env (Modalcell.id lock) in
  Permute { perm; env; level; ctx = Ordered.lock ctx ~parametric lock }

let raw_length (Permute { perm; ctx; _ }) = N.perm_dom (Ordered.raw_length ctx) perm
let level (Permute { level; _ }) = level
let mode (Permute { ctx; _ }) = Ordered.mode ctx

let maybe_lock ctx fa =
  if locking fa then
    let (Wrap modality) = Modality.locker (mode ctx) in
    lock ctx ~parametric:true modality
  else ctx

let locked (Permute { ctx; _ }) = Ordered.locked ctx

let empty mode =
  Permute { perm = N.id_perm N.zero; env = Emp (mode, D.zero); level = 0; ctx = Ordered.empty mode }

let dbwd (Permute { ctx; _ }) = Ordered.dbwd ctx
let apps (Permute { ctx; _ }) = Ordered.apps ctx

(* Lookup is the only place where the permutations are used nontrivially: we apply the permutation to the raw index before looking it up. *)
let lookup (Permute { perm; ctx; _ }) i = Ordered.lookup ctx (N.perm_apply perm (fst i), snd i)
let find_level (Permute { ctx; _ }) x = Ordered.find_level ctx x

(* To get the environment, we can now just return the precomputed one. *)
let env (Permute { env; _ }) = env

let ext (Permute { perm; env; level; ctx }) modality xs ty =
  let ctx, b = Ordered.ext ctx modality xs ty in
  Permute
    {
      perm = Insert (perm, Top);
      env = LazyExt (env, D.zero_plus D.zero, modality, Ordered.env_entry (CubeOf.singleton b));
      level = level + 1;
      ctx;
    }

let ext_let (Permute { perm; env; level; ctx }) modality xs tm =
  let ctx, b = Ordered.ext_let ctx modality xs tm in
  Permute
    {
      perm = Insert (perm, Top);
      env = LazyExt (env, D.zero_plus D.zero, modality, Ordered.env_entry (CubeOf.singleton b));
      level = level + 1;
      ctx;
    }

(* Remove the last cube entry in a context.  This only works if it is a pure cube variable with no fields and the context has not been permuted after its addition. *)
type (_, _, _) pop =
  | Pop :
      ('mode, 'a, 'b) t * ('a N.suc, 'asuc) Eq.t * (('b, 'n) snoc, 'bn) Eq.t
      -> ('mode, 'asuc, 'bn) pop

let pop : type mode a b. (mode, a, b) t -> ((mode, a, b) pop, string) Result.t =
 fun (Permute { ctx; perm; level; env }) ->
  match (Ordered.pop ctx, perm, env) with
  | Some (Pop (ctx, Eq, Eq)), Insert (perm, Top), LazyExt (env, _, _, _) ->
      Ok (Pop (Permute { ctx; perm; level; env }, Eq, Eq))
  | Some (Pop (ctx, Eq, Eq)), Insert (perm, Top), Ext (env, _, _, _) ->
      Ok (Pop (Permute { ctx; perm; level; env }, Eq, Eq))
  | Some (Pop (ctx, Eq, Eq)), Id, LazyExt (env, _, _, _) ->
      Ok (Pop (Permute { ctx; perm = Id; level; env }, Eq, Eq))
  | Some (Pop (ctx, Eq, Eq)), Id, Ext (env, _, _, _) ->
      Ok (Pop (Permute { ctx; perm = Id; level; env }, Eq, Eq))
  | Some (Pop (_, Eq, Eq)), _, Permute _ -> Error "env is permuted"
  | Some (Pop (_, Eq, Eq)), _, Act _ -> Error "env is acted"
  | Some (Pop (_, Eq, Eq)), _, Key _ -> Error "env is keyed"
  | Some (Pop (_, Eq, Eq)), _, Shift _ -> Error "env is shifted"
  | Some (Pop (_, Eq, Eq)), _, Unshift _ -> Error "env is unshifted"
  | Some (Pop (_, Eq, Eq)), Insert (_, Pop _), _ -> Error "nonidentity permutation"
  | None, _, _ -> Error "empty or locked"

let lam (Permute { ctx; _ }) tm = Ordered.lam ctx tm

let forget_levels (Permute { perm; ctx; level; _ }) forget =
  let ctx = Ordered.forget_levels ctx forget in
  Permute { perm; env = Ordered.env ctx; level; ctx }

(* Augment an ordered context by the identity permutation *)
let of_ordered ?level ctx =
  let level =
    match level with
    | None -> Ordered.length ctx
    | Some level -> level in
  Permute { perm = N.id_perm (Ordered.raw_length ctx); env = Ordered.env ctx; level; ctx }

(* Peel off enough locks to make up a supplied modality, along with any entries between them. *)
type (_, _) remove_lock =
  | Remove_lock : ('cod, 'a, 'b) t * ('b, 'c, 'bc) Tbwd.append -> ('cod, 'bc) remove_lock

let remove_lock : type mode modality cod a bc.
    (mode, a, bc) t -> (mode, modality, cod) Modality.t -> (cod, bc) remove_lock =
 fun (Permute { ctx; level; _ }) modality ->
  let (Remove_lock (ctx, bc)) = Ordered.remove_lock ctx modality in
  (* We save the level of the old, longer, context, so that when new level variables are created in the new shorter context there's no chance they'll conflict with level variables from the old context.  *)
  Remove_lock (of_ordered ~level ctx, bc)
