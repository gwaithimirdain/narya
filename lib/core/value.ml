open Util
open Tbwd
open Dim
open Dimbwd
include Energy
open Term
open Reporter

type inst = private Dummy_inst
type noninst = private Dummy_noninst

(* ******************** Values ******************** *)

(* A De Bruijn level is a pair of integers: one for the position (counting in) of the cube-variable-bundle in the context, and one that counts through the faces of that bundle. *)
type level = int * int

(* Internal values, the result of evaluation, with closures for abstractions.  Use De Bruijn *levels*, so that weakening is implicit.  Fully internal unbiased syntax lives here: in addition to higher-dimensional applications and abstractions, we also have higher-dimensional pi-types, higher-dimensional universes, and instantiations of higher-dimensional types.  Separated into neutrals and normals, so that there are no beta-redexes.  Explicit substitutions (environments) are stored on binders, for NBE. *)

(* The codomains of a pi-type are stored as a Cube of binders, and since binders are a type family this dependence has to be specified by applying a module functor (rather than just parametrizing a type).  Since values are defined mutually with binders, we need to "apply the functor Cube" mutually with the definition of these types.  This is possible using a recursive module. *)
module rec Value : sig
  (* A recursive module is required to specify its module type explicitly.  We make this as transparent as possible, so the module type is nearly a copy of the module itself.  For the comments, see the actual definition below. *)
  module BindFam : sig
    type ('k, 'b) t = ('k, kinetic) Value.binder
  end

  module BindCube : module type of Cube (BindFam)

  module Structfield : sig
    type (_, _) t =
      (* We remember which fields are labeled, for readback purposes, and we store the value of each field lazily, so that corecursive definitions don't try to compute an entire infinite structure.  And since in the non-kinetic case, evaluation can produce more data than just a term (e.g. whether a case tree has yet reached a leaf), what we store lazily is the result of evaluation. *)
      | Lower : 's Value.lazy_eval * [ `Labeled | `Unlabeled ] -> (D.zero, 'n * 's * 'et) t
      (* In the higher case, they are always labeled.  There are multiple values are indexed by insertions, regarded as partial bijections with zero remaining dimensions; the 'evaluation dimension is the substitution dimension 'n and the 'intrinsic dimension is associated to the field.  We also store the original terms as a closure, since they may be needed to evaluate fields of degeneracies. *)
      | Higher : ('m, 'n, 'mn, 'p, 'i, 'a) higher_data -> ('i, 'p * potential * no_eta) t

    and ('m, 'n, 'mn, 'p, 'i, 'a) higher_data = {
      vals : ('p, 'i, potential Value.lazy_eval option) InsmapOf.t;
      intrinsic : 'i D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      env : ('m, 'a) Value.env;
      deg : ('p, 'mn) deg;
      terms : ('n, 'i, 'a) PlusPbijmap.t;
    }
  end

  module StructfieldAbwd : module type of Field.Abwd (Structfield)

  type head =
    | Var : { level : level; deg : ('m, 'n) deg } -> head
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> head
    | Meta : {
        meta : ('a, 'b, 's) Meta.t;
        env : ('m, 'b) env;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> head
    | UU : 'n D.t -> head
    | Pi : string option * ('k, kinetic value) CubeOf.t * ('k, unit) BindCube.t -> head

  and _ apps =
    | Emp : noninst apps
    | Arg : 'any apps * ('n, normal) CubeOf.t * ('nk, 'n, 'k) insertion -> noninst apps
    | Field : 'any apps * 'i Field.t * ('t, 'i, 'n) D.plus * ('tk, 't, 'k) insertion -> noninst apps
    | Inst : noninst apps * 'k D.pos * ('n, 'k, 'nk, normal) TubeOf.t -> inst apps

  and (_, _) binder =
    | Bind : {
        env : ('m, 'a) env;
        body : (('a, 'n) snoc, 's) term;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> ('mn, 's) binder

  and _ value =
    | Neu : {
        head : head;
        args : 'any apps;
        value : potential lazy_eval;
        ty : kinetic value Lazy.t;
      }
        -> kinetic value
    | Constr : Constr.t * 'n D.t * ('n, kinetic value) CubeOf.t list -> kinetic value
    | Lam : 'k variables * ('k, 's) binder -> 's value
    | Struct : ('p * 's * 'et) StructfieldAbwd.t * ('pk, 'p, 'k) insertion * 's energy -> 's value
    | Canonical : 'mk canonical * ('m, 'k, 'mk, normal) TubeOf.t -> potential value

  and _ evaluation =
    | Val : 's value -> 's evaluation
    | Realize : kinetic value -> potential evaluation
    | Unrealized : potential evaluation

  and _ canonical =
    | UU : 'm D.t -> 'm canonical
    | Pi : string option * ('m, kinetic value) CubeOf.t * ('m, unit) BindCube.t -> 'm canonical
    | Data : ('m, 'j, 'ij) data_args -> 'm canonical
    | Codata : ('mn, 'm, 'n, 'c, 'a, 'et) codata_args -> 'mn canonical

  and ('m, 'j, 'ij) data_args = {
    dim : 'm D.t;
    tyfam : normal Lazy.t option ref;
    indices : (('m, normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    constrs : (Constr.t, ('m, 'ij) dataconstr) Abwd.t;
    discrete : [ `Yes | `Maybe | `No ];
  }

  and ('mn, 'm, 'n, 'c, 'a, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    env : ('m, 'a) env;
    termctx : ('c, ('a, 'n) snoc) termctx option Lazy.t;
    ins : ('mn, 'm, 'n) insertion;
    fields : ('a * 'n * 'et) Term.CodatafieldAbwd.t;
  }

  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('m, 'a) env;
        args : ('a, 'p, 'ap) Telescope.t;
        indices : (('ap, kinetic) term, 'ij) Vec.t;
      }
        -> ('m, 'ij) dataconstr

  and normal = { tm : kinetic value; ty : kinetic value }

  and (_, _) env =
    | Emp : 'n D.t -> ('n, emp) env
    | LazyExt :
        ('n, 'b) env * ('n, 'k, 'nk) D.plus * ('nk, kinetic lazy_eval) CubeOf.t
        -> ('n, ('b, 'k) snoc) env
    | Ext :
        ('n, 'b) env * ('n, 'k, 'nk) D.plus * (('nk, kinetic value) CubeOf.t, Code.t) Result.t
        -> ('n, ('b, 'k) snoc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
    | Permute : ('a, 'b) Tbwd.permute * ('n, 'b) env -> ('n, 'a) env
    | Shift : ('mn, 'b) env * ('m, 'n, 'mn) D.plus * ('n, 'b, 'nb) Plusmap.t -> ('m, 'nb) env

  and 's lazy_state =
    | Deferred_eval :
        ('m, 'b) env * ('b, 's) term * ('mn, 'm, 'n) insertion * 'any apps
        -> 's lazy_state
    | Deferred : (unit -> 's evaluation) * ('m, 'n) deg * 'any apps -> 's lazy_state
    | Ready : 's evaluation -> 's lazy_state

  and 's lazy_eval = 's lazy_state ref
end = struct
  (* Here is the recursive application of the functor Cube.  First we define a module to pass as its argument, with type defined to equal the yet-to-be-defined binder, referred to recursively. *)
  module BindFam = struct
    type ('k, 'b) t = ('k, kinetic) Value.binder
  end

  module BindCube = Cube (BindFam)

  module Structfield = struct
    type (_, _) t =
      (* We remember which fields are labeled, for readback purposes, and we store the value of each field lazily, so that corecursive definitions don't try to compute an entire infinite structure.  And since in the non-kinetic case, evaluation can produce more data than just a term (e.g. whether a case tree has yet reached a leaf), what we store lazily is the result of evaluation. *)
      | Lower : 's Value.lazy_eval * [ `Labeled | `Unlabeled ] -> (D.zero, 'n * 's * 'et) t
      (* In the higher case, they are always labeled.  There are multiple values are indexed by insertions, regarded as partial bijections with zero remaining dimensions; the 'evaluation dimension is the substitution dimension 'n and the 'intrinsic dimension is associated to the field.  We also store the original terms as a closure, since they may be needed to evaluate fields of degeneracies. *)
      | Higher : ('m, 'n, 'mn, 'p, 'i, 'a) higher_data -> ('i, 'p * potential * no_eta) t

    and ('m, 'n, 'mn, 'p, 'i, 'a) higher_data = {
      vals : ('p, 'i, potential Value.lazy_eval option) InsmapOf.t;
      intrinsic : 'i D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      env : ('m, 'a) Value.env;
      deg : ('p, 'mn) deg;
      terms : ('n, 'i, 'a) PlusPbijmap.t;
    }
  end

  module StructfieldAbwd = Field.Abwd (Structfield)

  (* The head of an elimination spine is a variable, a constant, or a substituted metavariable.  *)
  type head =
    (* A variable is determined by a De Bruijn LEVEL, and stores a neutral degeneracy applied to it. *)
    | Var : { level : level; deg : ('m, 'n) deg } -> head
    (* A constant also stores a dimension that it is substituted to and a neutral insertion applied to it.  Many constants are zero-dimensional, meaning that 'c' is zero, and hence a=b is just a dimension and the insertion is trivial.  The dimension of a constant is its dimension as a term standing on its own; so in particular if it has any parameters, then it belongs to an ordinary, 0-dimensional, pi-type and therefore is 0-dimensional, even if the eventual codomain of the pi-type is higher-dimensional.  Note also that when nonidentity insertions end up getting stored here, e.g. by Act, the dimension 'c gets extended as necessary; so it is always okay to create a constant with the (0,0,0) insertion to start with, even if you don't know what its actual dimension is. *)
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> head
    (* A metavariable (i.e. flexible) head stores the metavariable along with a delayed substitution applied to it. *)
    | Meta : {
        meta : ('a, 'b, 's) Meta.t;
        env : ('m, 'b) env;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> head
    (* Universes are parametrized by a dimension *)
    | UU : 'n D.t -> head
    (* Pis must store not just the domain type but all its boundary types.  These domain and boundary types are not fully instantiated.  Note the codomains are stored in a cube of binders. *)
    | Pi : string option * ('k, kinetic value) CubeOf.t * ('k, unit) BindCube.t -> head

  (* An application contains the data of an n-dimensional argument and its boundary, together with a neutral insertion applied outside that can't be pushed in.  This represents the *argument list* of a single application, not the function.  Thus, an application spine will be a head together with a list of apps. *)
  and _ apps =
    | Emp : noninst apps
    | Arg : 'any apps * ('n, normal) CubeOf.t * ('nk, 'n, 'k) insertion -> noninst apps
    (* For a higher field with ('n, 't, 'i) insertion, the actual evaluation dimension is 'n, but the result dimension is only 't.  So the dimension of the arg is 't, since that's the output dimension that a degeneracy acting on could be pushed through.  However, since a degeneracy of dimension up to 'n can act on the inside, we can push in the whole insertion and store only a plus outside. *)
    | Field : 'any apps * 'i Field.t * ('t, 'i, 'n) D.plus * ('tk, 't, 'k) insertion -> noninst apps
    (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial in dimensions, so it should not be applied more than once in a row.  So the dummy parameter of 'apps' tracks whether the last application was an instantiation, and here we verify that it wasn't before instantiating.  We also allow only nontrivial instantiations, to avoid cluttering up application spines with lots of empty instantiations and simplify equality-checking. *)
    | Inst : noninst apps * 'k D.pos * ('n, 'k, 'nk, normal) TubeOf.t -> inst apps

  (* Lambdas and Pis both bind a variable, along with its dependencies.  These are recorded as defunctionalized closures.  Since they are produced by higher-dimensional substitutions and operator actions, the dimension of the binder can be different than the dimension of the environment that closes its body.  Accordingly, in addition to the environment and degeneracy to close its body, we store information about how to map the eventual arguments into the bound variables in the body.  *)
  and (_, _) binder =
    | Bind : {
        env : ('m, 'a) env;
        body : (('a, 'n) snoc, 's) term;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> ('mn, 's) binder

  and _ value =
    (* A neutral is an application spine: a head with a list of applications.  It also stores its type, and (lazily) the up-to-now result of evaluating that application spine.  The type is also lazy because the 0-dimensional universe is morally an infinite data structure Uninst (UU 0, (Uninst (UU 0, Uninst (UU 0, ... )))).  If that result is "Unrealized", then it is a "true neutral", the sort of neutral that is permanently stuck and usually appears in paper proofs of normalization.  If it is "Val" then the spine is still waiting for further arguments for its case tree to compute.  If it is "Realized" then the case tree has already evaluated to an ordinary value; this should only happen when glued evaluation is in effect. *)
    | Neu : {
        head : head;
        args : 'any apps;
        value : potential lazy_eval;
        ty : kinetic value Lazy.t;
      }
        -> kinetic value
    (* A constructor has a name, a dimension, and a list of arguments of that dimension.  It must always be applied to the correct number of arguments (otherwise it can be eta-expanded).  It doesn't have an outer insertion because a primitive datatype is always 0-dimensional (it has higher-dimensional versions, but degeneracies can always be pushed inside these).  *)
    | Constr : Constr.t * 'n D.t * ('n, kinetic value) CubeOf.t list -> kinetic value
    | Lam : 'k variables * ('k, 's) binder -> 's value
    (* Structs have to store an insertion outside, like an application, to deal with higher-dimensional record types like Gel.  Here 'k is the Gel dimension, with 'n the substitution dimension and 'nk the total dimension. *)
    | Struct : ('p * 's * 'et) StructfieldAbwd.t * ('pk, 'p, 'k) insertion * 's energy -> 's value
    (* A canonical type is only a *potential* value, so it appears as the 'value' of a 'neu'.  It may also be partially instantiated. *)
    | Canonical : 'mk canonical * ('m, 'k, 'mk, normal) TubeOf.t -> potential value

  (* This is the result of evaluating a term with a given kind of energy.  Evaluating a kinetic term just produces a (kinetic) value, whereas evaluating a potential term might be a potential value (waiting for more arguments), or else the information that the case tree has reached a leaf and the resulting kinetic value or canonical type, or else the information that the case tree is permanently stuck.  *)
  and _ evaluation =
    (* When 's = potential, a Val means the case tree is not yet fully applied; while when 's = kinetic, it is the only possible kind of result.  Collapsing these two together seems to unify the code for Lam and Struct as much as possible. *)
    | Val : 's value -> 's evaluation
    | Realize : kinetic value -> potential evaluation
    | Unrealized : potential evaluation

  (* A canonical type value is either a universe, a function-type, a datatype, or a codatatype/record.  It, is parametrized by its dimension as a type, which might be larger than its evaluation dimension if it has an intrinsic dimension (e.g. Gel). *)
  and _ canonical =
    (* At present, we never produce these except as the values of their corresponding heads.  But in principle, we could allow universes and pi-types as potential terms, so that constants could be defined to "behave like" universes or pi-types without reducing to them. *)
    | UU : 'm D.t -> 'm canonical
    | Pi : string option * ('m, kinetic value) CubeOf.t * ('m, unit) BindCube.t -> 'm canonical
    (* We define a named record type to encapsulate the arguments of Data, rather than using an inline one, so that we can bind its existential variables (https://discuss.ocaml.org/t/annotating-by-an-existential-type/14721).  See the definition below. *)
    | Data : ('m, 'j, 'ij) data_args -> 'm canonical
    (* A codatatype value has an eta flag, an environment that it was evaluated at, an insertion that relates its intrinsic dimension (such as for Gel) to the dimension it was evaluated at, and its fields as unevaluted terms that depend on one additional variable belonging to the codatatype itself (usually through its previous fields).  Note that combining env, ins, and any of the field terms in a *lower* codatafield produces the data of a binder; so in the absence of higher codatatypes we can think of this as a family of binders, one for each field, that share the same environment and insertion.  (But with higher fields this is no longer the case, as the context of the types gets degenerated by their dimension.) *)
    | Codata : ('mn, 'm, 'n, 'c, 'a, 'et) codata_args -> 'mn canonical

  (* A datatype value stores: *)
  and ('m, 'j, 'ij) data_args = {
    (* The dimension to which it is substituted *)
    dim : 'm D.t;
    (* The datatype family after being applied to the parameters but not the indices, e.g. "Vec A".  This is an option ref because it gets set a little later than the rest of the fields are computed, since only when working with the embedding of neutrals into normals do we have the application spine and its type available.  *)
    tyfam : normal Lazy.t option ref;
    (* The indices applied so far, and the number remaining *)
    indices : (('m, normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    (* All the constructors *)
    constrs : (Constr.t, ('m, 'ij) dataconstr) Abwd.t;
    (* Whether it is discrete.  The value `Maybe means that it could be discrete based on its own parameters, indices, and constructor arguments, but either is waiting for its mutual companions to be typechecked, or at least one of them failed to be discrete.  Thus for equality-testing purposes, `Maybe is treated like `No. *)
    discrete : [ `Yes | `Maybe | `No ];
  }

  and ('mn, 'm, 'n, 'c, 'a, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    env : ('m, 'a) env;
    termctx : ('c, ('a, 'n) snoc) termctx option Lazy.t;
    ins : ('mn, 'm, 'n) insertion;
    fields : ('a * 'n * 'et) Term.CodatafieldAbwd.t;
  }

  (* Each constructor stores the telescope of types of its arguments, as a closure, and the index values as function values taking its arguments. *)
  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('m, 'a) env;
        args : ('a, 'p, 'ap) Telescope.t;
        indices : (('ap, kinetic) term, 'ij) Vec.t;
      }
        -> ('m, 'ij) dataconstr

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and normal = { tm : kinetic value; ty : kinetic value }

  (* An "environment" is a context morphism *from* a De Bruijn LEVEL context *to* a (typechecked) De Bruijn INDEX context.  Specifically, an ('n, 'a) env is an 'n-dimensional substitution from a level context to an index context indexed by the hctx 'a.  Since the index context could have some variables that are labeled by integers together with faces, the values also have to allow that. *)
  and (_, _) env =
    | Emp : 'n D.t -> ('n, emp) env
    (* The (n+k)-cube here is morally a k-cube of n-cubes, representing a k-dimensional "cube variable" consisting of some number of "real" variables indexed by the faces of a k-cube, each of which has an n-cube of values representing a value and its boundaries.  But this contains the same data as an (n+k)-cube since a strict face of (n+k) decomposes uniquely as a strict face of n plus a strict face of k, and it seems to be more convenient to store it as a single (n+k)-cube. *)
    (* We have two kinds of variable bindings in an environment: lazy and non-lazy. *)
    | LazyExt :
        ('n, 'b) env * ('n, 'k, 'nk) D.plus * ('nk, kinetic lazy_eval) CubeOf.t
        -> ('n, ('b, 'k) snoc) env
    (* We also allow Error binding in an environment, indicating that that variable is not actually usable, usually due to an earlier error in typechecking that we've continued on from anyway.  *)
    | Ext :
        ('n, 'b) env * ('n, 'k, 'nk) D.plus * (('nk, kinetic value) CubeOf.t, Code.t) Result.t
        -> ('n, ('b, 'k) snoc) env
    | Act : ('n, 'b) env * ('m, 'n) op -> ('m, 'b) env
    | Permute : ('a, 'b) Tbwd.permute * ('n, 'b) env -> ('n, 'a) env
    (* Adding a dimension 'n to all the dimensions in a dimension list 'b is the power/cotensor in the dimension-enriched category of contexts.  Shifting an environment (substitution) implements its universal property: an (m+n)-dimensional substitution with codomain b is equivalent to an m-dimensional substitution with codomain n+b. *)
    | Shift : ('mn, 'b) env * ('m, 'n, 'mn) D.plus * ('n, 'b, 'nb) Plusmap.t -> ('m, 'nb) env

  (* An 's lazy_eval behaves from the outside like an 's evaluation Lazy.t.  But internally, in addition to being able to store an arbitrary thunk, it can also store a term and an environment in which to evaluate it (plus an outer insertion that can't be pushed into the environment).  This allows it to accept degeneracy actions and incorporate them into the environment, so that when it's eventually forced the term only has to be traversed once.  It can also accumulate degeneracies on an arbitrary thunk (which could, of course, be a constant value that was already forced, but now is deferred again until it's done accumulating degeneracy actions).  Both kinds of deferred values can also store more arguments and field projections for it to be applied to; this is only used in glued evaluation. *)
  and 's lazy_state =
    | Deferred_eval :
        ('m, 'b) env * ('b, 's) term * ('mn, 'm, 'n) insertion * 'any apps
        -> 's lazy_state
    | Deferred : (unit -> 's evaluation) * ('m, 'n) deg * 'any apps -> 's lazy_state
    | Ready : 's evaluation -> 's lazy_state

  and 's lazy_eval = 's lazy_state ref
end

include Value

type any_canonical = Any : 'm canonical -> any_canonical

(* Every context morphism has a valid dimension. *)
let rec dim_env : type n b. (n, b) env -> n D.t = function
  | Emp n -> n
  | Ext (e, _, _) -> dim_env e
  | LazyExt (e, _, _) -> dim_env e
  | Act (_, op) -> dom_op op
  | Permute (_, e) -> dim_env e
  | Shift (e, mn, _) -> D.plus_left mn (dim_env e)

(* And likewise every binder *)
let dim_binder : type m s. (m, s) binder -> m D.t = function
  | Bind b -> dom_ins b.ins

let dim_canonical : type m. m canonical -> m D.t = function
  | UU dim -> dim
  | Pi (_, doms, _) -> CubeOf.dim doms
  | Data { dim; _ } -> dim
  | Codata { ins; _ } -> dom_ins ins

(* The length of an environment is a tbwd of dimensions. *)
let rec length_env : type n b. (n, b) env -> b Dbwd.t = function
  | Emp _ -> Word Zero
  | Ext (env, nk, _) ->
      let (Word le) = length_env env in
      Word (Suc (le, D.plus_right nk))
  | LazyExt (env, nk, _) ->
      let (Word le) = length_env env in
      Word (Suc (le, D.plus_right nk))
  | Act (env, _) -> length_env env
  | Permute (p, env) -> Plusmap.OfDom.permute p (length_env env)
  | Shift (env, mn, nb) -> Plusmap.out (D.plus_right mn) (length_env env) nb

(* Smart constructor that composes actions and cancels identities *)
let rec act_env : type m n b. (n, b) env -> (m, n) op -> (m, b) env =
 fun env s ->
  match env with
  | Act (env, s') -> act_env env (comp_op s' s)
  | _ -> (
      match is_id_op s with
      | Some Eq -> env
      | None -> Act (env, s))

(* Create a lazy evaluation *)
let lazy_eval : type n b s. (n, b) env -> (b, s) term -> s lazy_eval =
 fun env tm -> ref (Deferred_eval (env, tm, ins_zero (dim_env env), Emp))

let defer : type s. (unit -> s evaluation) -> s lazy_eval =
 fun tm -> ref (Deferred (tm, id_deg D.zero, Emp))

let ready : type s. s evaluation -> s lazy_eval = fun ev -> ref (Ready ev)

let apply_lazy : type n s. s lazy_eval -> (n, normal) CubeOf.t -> s lazy_eval =
 fun lev xs ->
  let xins = ins_zero (CubeOf.dim xs) in
  match !lev with
  | Deferred_eval (env, tm, ins, apps) -> ref (Deferred_eval (env, tm, ins, Arg (apps, xs, xins)))
  | Deferred (tm, ins, apps) -> ref (Deferred (tm, ins, Arg (apps, xs, xins)))
  | Ready tm -> ref (Deferred ((fun () -> tm), id_deg D.zero, Arg (Emp, xs, xins)))

(* We defer "field_lazy" to act.ml, since it requires pushing a permutation inside the apps. *)

(* Given a De Bruijn level and a type, build the variable of that level having that type. *)
let var : level -> kinetic value -> kinetic value =
 fun level ty ->
  Neu
    {
      head = Var { level; deg = id_deg D.zero };
      args = Emp;
      value = ready Unrealized;
      ty = Lazy.from_val ty;
    }

(* Project out a cube or tube of values from a cube or tube of normals *)
let val_of_norm_cube : type n. (n, normal) CubeOf.t -> (n, kinetic value) CubeOf.t =
 fun arg -> CubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

let val_of_norm_tube : type n k nk.
    (n, k, nk, normal) TubeOf.t -> (n, k, nk, kinetic value) TubeOf.t =
 fun arg -> TubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

(* Remove an entry from an environment *)
let rec remove_env : type a k b n. (n, b) env -> (a, k, b) Tbwd.insert -> (n, a) env =
 fun env v ->
  match (env, v) with
  | Emp _, _ -> .
  | Act (env, op), _ -> Act (remove_env env v, op)
  | Permute (p, env), _ ->
      let (Permute_insert (v', p')) = Tbwd.permute_insert v p in
      Permute (p', remove_env env v')
  | Ext (env, nk, xs), Later v -> Ext (remove_env env v, nk, xs)
  | LazyExt (env, nk, xs), Later v -> LazyExt (remove_env env v, nk, xs)
  | Ext (env, _, _), Now -> env
  | LazyExt (env, _, _), Now -> env
  | Shift (env, mn, nb), _ ->
      let (Unmap_insert (_, v', na)) = Plusmap.unmap_insert v nb in
      Shift (remove_env env v', mn, na)

(* The universe of any dimension belongs to an instantiation of itself.  Note that the result is not itself a type (i.e. in the 0-dimensional universe) unless n=0.  This is the universe itself as a term. *)
let rec universe : type n. n D.t -> kinetic value =
 fun n ->
  Neu
    {
      head = UU n;
      args = Emp;
      value = ready (Val (Canonical (UU n, TubeOf.empty n)));
      ty = lazy (universe_ty n);
    }

and universe_nf : type n. n D.t -> normal = fun n -> { tm = universe n; ty = universe_ty n }

(* And this is the instantiation of itself that it belongs to.  This is a type (i.e. an element of the 0-dimensional universe), so it must be fully instantiated.  *)
and universe_ty : type n. n D.t -> kinetic value =
 fun n ->
  match D.compare_zero n with
  | Zero -> universe D.zero
  | Pos n' ->
      let args =
        TubeOf.build D.zero (D.zero_plus n)
          {
            build =
              (fun fa ->
                let m = dom_tface fa in
                universe_nf m);
          } in
      let value = ready (Val (Canonical (UU n, args))) in
      Neu { head = UU n; args = Inst (Emp, n', args); value; ty = lazy (universe D.zero) }

type any_apps = Any : 'any apps -> any_apps

(* Smart constructor that coalesces instantiations *)
let inst_apps : type any m n mn. any apps -> (m, n, mn, normal) TubeOf.t -> any_apps =
 fun apps args2 ->
  let n = TubeOf.inst args2 in
  match D.compare_zero n with
  | Zero -> Any apps
  | Pos n' -> (
      match apps with
      | Inst (apps, k, args1) -> (
          let (Plus nk) = D.plus (TubeOf.inst args1) in
          match D.compare (TubeOf.uninst args1) (TubeOf.out args2) with
          | Neq -> fatal (Dimension_mismatch ("inst_apps", TubeOf.uninst args1, TubeOf.out args2))
          | Eq ->
              let args = TubeOf.plus_tube nk args1 args2 in
              Any (Inst (apps, D.plus_pos n k nk, args)))
      | Emp -> Any (Inst (apps, n', args2))
      | Arg _ -> Any (Inst (apps, n', args2))
      | Field _ -> Any (Inst (apps, n', args2)))

(* Instantiate a lazy value *)
let inst_lazy : type m n mn s. s lazy_eval -> (m, n, mn, normal) TubeOf.t -> s lazy_eval =
 fun lev args ->
  match D.compare_zero (TubeOf.inst args) with
  | Zero -> lev
  | Pos k -> (
      match !lev with
      | Deferred_eval (env, tm, ins, apps) ->
          let (Any newargs) = inst_apps apps args in
          ref (Deferred_eval (env, tm, ins, newargs))
      | Deferred (tm, ins, apps) ->
          let (Any newargs) = inst_apps apps args in
          ref (Deferred (tm, ins, newargs))
      | Ready tm -> ref (Deferred ((fun () -> tm), id_deg D.zero, Inst (Emp, k, args))))

(* Given a *type*, hence an element of a fully instantiated universe, extract the arguments of the instantiation of that universe. *)
let inst_tys : kinetic value -> kinetic value TubeOf.full = function
  | Neu { ty = (lazy (Neu { args = Inst (_, _, tys); _ })); _ } -> (
      match D.compare (TubeOf.uninst tys) D.zero with
      | Eq ->
          let Eq = D.plus_uniq (D.zero_plus (TubeOf.inst tys)) (TubeOf.plus tys) in
          Full_tube (val_of_norm_tube tys)
      | Neq -> fatal (Anomaly "universe must be fully instantiated to be a type"))
  | _ -> fatal (Anomaly "invalid type, has no instantiation arguments")

(* Split off an instantiation, if any, at the end of an apps *)
let inst_of_apps : type any. any apps -> noninst apps * normal TubeOf.any option =
 fun apps ->
  match apps with
  | Inst (base_args, _, args1) -> (base_args, Some (TubeOf.Any_tube args1))
  | Emp -> (apps, None)
  | Arg _ -> (apps, None)
  | Field _ -> (apps, None)

module Fwd_app = struct
  (* Make an apps without instantiations into a forwards list *)
  type t =
    | Arg : ('n, normal) CubeOf.t * ('nk, 'n, 'k) insertion -> t
    | Field : 'i Field.t * ('t, 'i, 'n) D.plus * ('tk, 't, 'k) insertion -> t

  let snoc : type any. any apps -> t -> noninst apps =
   fun apps app ->
    match app with
    | Arg (arg, ins) -> Arg (apps, arg, ins)
    | Field (fld, plus, ins) -> Field (apps, fld, plus, ins)

  let of_apps apps =
    let rec go : type any. any apps -> t list -> t list =
     fun apps fwds ->
      match apps with
      | Emp -> fwds
      | Arg (apps, arg, ins) -> go apps (Arg (arg, ins) :: fwds)
      | Field (apps, fld, plus, ins) -> go apps (Field (fld, plus, ins) :: fwds)
      | Inst _ -> fatal (Anomaly "instantiation in fwd_of_apps") in
    go apps []
end

(* Given two apps, the second longer, split the second into one of the same length and the rest. *)
let split_apps_at_length : type any1 any2.
    any1 apps -> any2 apps -> (noninst apps * Fwd_app.t list) option =
 fun apps1 apps2 ->
  let rec go apps2 fwd1 fwd2 =
    match (fwd1, fwd2) with
    | [], _ -> Some (apps2, fwd2)
    | _ :: fwd1, app2 :: fwd2 -> go (Fwd_app.snoc apps2 app2) fwd1 fwd2
    | _ -> None in
  go Emp (Fwd_app.of_apps apps1) (Fwd_app.of_apps apps2)

let get_full_tube : type n k nk a any.
    err:(n D.pos -> Code.t) ->
    ?severity:Asai.Diagnostic.severity ->
    (any * (n, k, nk, a) TubeOf.t) option ->
    a TubeOf.full =
 fun ~err ?(severity = Asai.Diagnostic.Bug) args ->
  match args with
  | None -> TubeOf.Full_tube (TubeOf.empty D.zero)
  | Some (_, args) -> (
      match D.compare_zero (TubeOf.uninst args) with
      | Pos n -> fatal ~severity (err n)
      | Zero ->
          let Eq = D.plus_uniq (TubeOf.plus args) (D.zero_plus (TubeOf.inst args)) in
          TubeOf.Full_tube args)

(* Glued evaluation is basically implemented, but currently disabled because it is very slow -- too much memory allocation, and OCaml 5 doesn't have memory profiling tools available yet to debug it.  So we disable it globally with this flag.  But all the regular tests pass with the flag enabled, and should continue to be run and to pass, so that once we are able to debug it it is still otherwise working. *)
module GluedEval = struct
  let toggle = false
  let read () = toggle
end
