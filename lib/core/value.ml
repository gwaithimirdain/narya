open Util
open Modal
open Tbwd
open Dim
open Tctx
include Energy
open Term
open Reporter

type inst = private Dummy_inst
type noninst = private Dummy_noninst

(* A phantom type parameter of neutral heads and application spines, recording whether the head is Failed or Live (see neu_head).  A failed head can only have an empty spine. *)
type failed = private Dummy_failed
type live = private Dummy_live

(* ******************** Values ******************** *)

(* A De Bruijn level is a pair of integers: one for the position (counting in) of the cube-variable-bundle in the context, and one that counts through the faces of that bundle. *)
type level = int * int

(* Internal values, the result of evaluation, with closures for abstractions.  Use De Bruijn *levels*, so that weakening is implicit.  Fully internal unbiased syntax lives here: in addition to higher-dimensional applications and abstractions, we also have higher-dimensional pi-types, higher-dimensional universes, and instantiations of higher-dimensional types.  Separated into neutrals and normals, so that there are no beta-redexes.  Explicit substitutions (environments) are stored on binders, for NBE. *)

(* The codomains of a pi-type are stored as a Cube of binders, and since binders are a type family this dependence has to be specified by applying a module functor (rather than just parametrizing a type).  Since values are defined mutually with binders, we need to "apply the functor Cube" mutually with the definition of these types.  This is possible using a recursive module. *)
module rec Value : sig
  (* A recursive module is required to specify its module type explicitly.  We make this as transparent as possible, so the module type is nearly a copy of the module itself.  For the comments, see the actual definition below. *)
  module BindFam : sig
    type (_, _) t =
      | BindFam :
          ('mode, 'modality, 'dom, 'n, kinetic) Value.binder
          -> ('n, 'mode * 'modality * 'dom) t
  end

  module BindCube : module type of Cube (BindFam)

  module Structfield : sig
    type (_, _) t =
      | Lower :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('gmode, 's) Value.lazy_eval
          * [ `Labeled | `Unlabeled ]
          -> (D.zero, 'mode * 'n * 's * 'et) t
      | Higher :
          ('mode, 'f, 'g, 'gmode, 'm, 'n, 'mn, 'p, 'i, 'ag) higher_data Lazy.t
          -> ('i, 'mode * 'p * potential * no_eta) t

    and ('mode, 'f, 'g, 'gmode, 'm, 'n, 'mn, 'p, 'i, 'ag) higher_data = {
      adj : ('mode, 'f, 'g, 'gmode) Modalcell.adjunction;
      vals : ('p, 'i, ('gmode, potential) Value.lazy_eval option) InsmapOf.t;
      intrinsic : 'i D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      env : ('gmode, 'm, 'ag) Value.env;
      deg : ('p, 'mn) deg;
      terms : ('n, 'i, 'gmode * 'ag) PlusPbijmap.t;
    }
  end

  module StructfieldAbwd : module type of Field.Abwd (Structfield)

  type (_, _, _) modal_value_cube =
    | Modal :
        ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
        * ('k, ('dom, 'a) Value.value) Dim.CubeOf.t
        -> ('n, 'mode, 'a) modal_value_cube

  type 'mode head =
    | Var : {
        level : level;
        deg : ('m, 'n) deg;
        key : ('mode, 'modality, 'lock, 'cod) Modalcell.t;
      }
        -> 'mode head
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> 'mode head
    | Meta : {
        meta : ('mode, 'a, 'b, 's) Meta.t;
        env : ('mode, 'm, 'b) env;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> 'mode head
    | UU : 'mode Mode.t * 'n D.t -> 'mode head
    | Pi : ('dom, 'modality, 'mode, 'n, 'm) pi_args -> 'mode head

  and (_, _) neu_head =
    | Failed : 'mode Mode.t -> ('mode, failed) neu_head
    | Live : 'mode head -> ('mode, live) neu_head

  and ('dom, 'modality, 'mode, 'n, 'm) pi_args = {
    x : 'n variables;
    filter : ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim;
    doms : ('n, ('dom, kinetic) value) CubeOf.t;
    cods : ('m, 'mode * 'modality * 'dom) BindCube.t;
  }

  and (_, _, _, _) apps =
    | Emp : ('mode, 'mode, noninst, 'fail) apps
    | Arg :
        ('hmode, 'mode, 'any, live) apps
        * ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim
        * ('n, 'dom normal) CubeOf.t
        * ('mk, 'm, 'k) insertion
        -> ('hmode, 'mode, noninst, live) apps
    | Field :
        ('hmode, 'src, 'any, live) apps
        * ('src, 'f, 'mode, 'ft, 't) Modality.filter_dim
        * 'i Field.t
        * ('t, 'i, 'n) D.plus
        * ('tk, 't, 'k) insertion
        -> ('hmode, 'mode, noninst, live) apps
    | Inst :
        ('hmode, 'mode, noninst, live) apps * 'k D.pos * ('n, 'k, 'nk, 'mode normal) TubeOf.t
        -> ('hmode, 'mode, inst, live) apps

  and (_, _, _, _, _) binder =
    | Bind : {
        env : ('mode, 'm, 'a) env;
        modality : ('dom, 'modality, 'mode) Modality.t;
        filter : ('dom, 'modality, 'mode, 'l, 'n) Modality.filter_dim;
        body : ('mode, ('a, ('modality, 'l) dim_entry) snoc, 's) term;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> ('mode, 'modality, 'dom, 'mn, 's) binder

  and (_, _) value =
    | Neu : {
        head : ('hmode, 'fail) neu_head;
        args : ('hmode, 'mode, 'any, 'fail) apps;
        value : ('mode, potential) lazy_eval;
        ty : ('mode, kinetic) value Lazy.t;
      }
        -> ('mode, kinetic) value
    | Constr :
        Constr.t * 'n D.t * ('n, 'mode, kinetic) modal_value_cube list
        -> ('mode, kinetic) value
    | Lam :
        'k variables
        * ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
        * ('mode, 'modality, 'dom, 'n, 's) binder
        -> ('mode, 's) value
    | Struct : ('mode, 'p, 'k, 'pk, 's, 'et) struct_args -> ('mode, 's) value
    | Canonical : ('mode, 'm, 'k, 'mk, 'e, 'n) inst_canonical -> ('mode, potential) value

  and ('mode, 'p, 'k, 'pk, 's, 'et) struct_args = {
    fields : ('mode * 'p * 's * 'et) StructfieldAbwd.t;
    ins : ('pk, 'p, 'k) insertion;
    energy : 's energy;
    eta : ('s, 'et) eta;
  }

  and ('mode, 'm, 'k, 'mk, 'e, 'n) inst_canonical = {
    mode : 'mode Mode.t;
    canonical : ('mode, 'e, 'n) canonical;
    ins : ('mk, 'e, 'n) insertion;
    tyargs : ('m, 'k, 'mk, 'mode normal) TubeOf.t;
    fields : ('mode * 'mk * potential * no_eta) StructfieldAbwd.t;
    mutable inst_fields : ('mode * 'm * potential * no_eta) StructfieldAbwd.t option;
  }

  and (_, _) evaluation =
    | Val : ('mode, 's) value -> ('mode, 's) evaluation
    | Realize : ('mode, kinetic) value -> ('mode, potential) evaluation
    | Unrealized : ('mode, potential) evaluation

  and (_, _, _) canonical =
    | UU : 'mode Mode.t * 'm D.t -> ('mode, 'm, D.zero) canonical
    | Pi : ('dom, 'modality, 'mode, 'n, 'm) pi_args -> ('mode, 'm, D.zero) canonical
    | Data : ('mode, 'm, 'j, 'ij) data_args -> ('mode, 'm, D.zero) canonical
    | Codata : ('mode, 'm, 'n, 'a, 'et) codata_args -> ('mode, 'm, 'n) canonical

  and ('mode, 'm, 'j, 'ij) data_args = {
    dim : 'm D.t;
    tyfam : ('mode, kinetic) lazy_eval;
    indices : (('m, 'mode normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    constrs : (Constr.t, ('mode, 'm) dataconstr) Abwd.t;
    recursive : Positivity.recursion;
    hints : hints;
  }

  and ('mode, 'm, 'n, 'a, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    hints : hints;
    env : ('mode, 'm, 'a) env;
    fields : ('mode * 'a * D.zero * 'n * 'et) Term.CodatafieldAbwd.t;
  }

  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('mode, 'm, 'a) env;
        ty : ('mode, 'a, kinetic) term;
        (* The function-type evaluated in env, computed lazily and cached, so that all the constructor applications checked, compared, or read back at one datatype value share a single evaluation of it.  It is acted on along with env. *)
        fnty : ('mode, kinetic) lazy_eval;
      }
        -> ('mode, 'm) dataconstr

  and 'mode normal = { tm : ('mode, kinetic) value; ty : ('mode, kinetic) value Lazy.t }

  and ('mk, 'dom) env_binding =
    [ `Lazy of ('mk, ('dom, kinetic) lazy_eval) CubeOf.t
    | `Ok of ('mk, ('dom, kinetic) value) CubeOf.t ]

  and (_, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'n, 'mode emp) env
    | Ext : {
        env : ('mode, 'n, 'b) env;
        plus : ('m, 'k, 'mk) D.plus;
        filter : ('dom, 'modality, 'mode, 'm, 'n) Modality.filter_dim;
        filtered : ('dom, 'modality, 'mode, 'k, 'k) Modality.filter_dim;
        values : ('mk, 'dom) env_binding;
      }
        -> ('mode, 'n, ('b, ('modality, 'k) dim_entry) snoc) env
    | Act : ('mode, 'n, 'b) env * ('m, 'n) opt_op -> ('mode, 'm, 'b) env
    | Lock :
        ('cod, 'n, 'b) env * ('dom, 'g, 'cod) Modality.gen
        -> ('dom, 'n, ('b, 'g lock_entry) snoc) env
    | Prekey : ('mode, 'n, 'b) env * ('mode, 'mu, 'nu, 'cod) Modalcell.t -> ('mode, 'n, 'b) env
    | Permute : ('a, 'b) permute * ('mode, 'n, 'b) env -> ('mode, 'n, 'a) env
    | Shift :
        ('mode, 'mn, 'b) env * ('m, 'n, 'mn) D.plus * ('n, 'b, 'nb, 'mode) plusmap
        -> ('mode, 'm, 'nb) env
    | Unshift :
        ('mode, 'm, 'nb) env * ('m, 'n, 'mn) D.plus * ('n, 'b, 'nb, 'mode) plusmap
        -> ('mode, 'mn, 'b) env

  and ('mode, 's) lazy_state =
    | Deferred_eval :
        ('mode, 'm, 'b) env
        * ('mode, 'b, 's) term
        * ('mn, 'm, 'n) insertion
        * ('mode, 'mu, 'nu, 'cod) Modalcell.t
        -> ('mode, 's) lazy_state
    | Deferred : (unit -> ('mode, 's) evaluation) -> ('mode, 's) lazy_state
    | Applied : ('hmode, 's) lazy_eval * ('hmode, 'mode) lazy_app -> ('mode, 's) lazy_state
    | Ready : ('mode, 's) evaluation -> ('mode, 's) lazy_state

  and ('mode, 's) lazy_eval = ('mode, 's) lazy_state ref

  and (_, _) lazy_app =
    | Apps : ('hmode, 'mode, 'any, live) apps -> ('hmode, 'mode) lazy_app
    | Action : ('m, 'n) deg * ('mode, 'mu, 'nu, 'cod) Modalcell.t -> ('mode, 'mode) lazy_app
end = struct
  (* Here is the recursive application of the functor Cube.  First we define a module to pass as its argument, with type defined to equal the yet-to-be-defined binder, referred to recursively. *)
  module BindFam = struct
    type (_, _) t =
      | BindFam :
          ('mode, 'modality, 'dom, 'n, kinetic) Value.binder
          -> ('n, 'mode * 'modality * 'dom) t
  end

  module BindCube = Cube (BindFam)

  module Structfield = struct
    type (_, _) t =
      (* We remember which fields are labeled, for readback purposes, and we store the value of each field lazily, so that corecursive definitions don't try to compute an entire infinite structure.  And since in the non-kinetic case, evaluation can produce more data than just a term (e.g. whether a case tree has yet reached a leaf), what we store lazily is the result of evaluation.  A lower struct field also stores the adjunction of the field: the value lives at the source mode of the right adjoint (behind a lock by the right adjoint, but values don't track their contexts).  Ordinary fields use the identity adjunction. *)
      | Lower :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('gmode, 's) Value.lazy_eval
          * [ `Labeled | `Unlabeled ]
          -> (D.zero, 'mode * 'n * 's * 'et) t
      (* In the higher case, they are always labeled.  There are multiple values are indexed by insertions, regarded as partial bijections with zero remaining dimensions; the 'evaluation dimension is the substitution dimension 'n and the 'intrinsic dimension is associated to the field.  We also store the original terms as a closure, since they may be needed to evaluate fields of degeneracies. *)
      | Higher :
          ('mode, 'f, 'g, 'gmode, 'm, 'n, 'mn, 'p, 'i, 'ag) higher_data Lazy.t
          -> ('i, 'mode * 'p * potential * no_eta) t

    and ('mode, 'f, 'g, 'gmode, 'm, 'n, 'mn, 'p, 'i, 'ag) higher_data = {
      adj : ('mode, 'f, 'g, 'gmode) Modalcell.adjunction;
      vals : ('p, 'i, ('gmode, potential) Value.lazy_eval option) InsmapOf.t;
      intrinsic : 'i D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      env : ('gmode, 'm, 'ag) Value.env;
      deg : ('p, 'mn) deg;
      terms : ('n, 'i, 'gmode * 'ag) PlusPbijmap.t;
    }
  end

  module StructfieldAbwd = Field.Abwd (Structfield)

  type (_, _, _) modal_value_cube =
    | Modal :
        ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
        * ('k, ('dom, 'a) Value.value) Dim.CubeOf.t
        -> ('n, 'mode, 'a) modal_value_cube

  (* The head of an elimination spine is a variable, a constant, or a substituted metavariable.  *)
  type 'mode head =
    (* A variable is determined by a De Bruijn LEVEL, and stores a neutral degeneracy applied to it, as well as a modal key 2-cell.  The vertical domain of the key is the modality annotating the variable in the context, and the vertical codomain is the composite of all the locks between that variable and the (rightmost) end of the context.  Accordingly, the horizontal codomain is the mode of the context at the time when the variable was added, and the horizontal domain is the mode of the current context. *)
    | Var : {
        level : level;
        deg : ('m, 'n) deg;
        key : ('mode, 'modality, 'lock, 'cod) Modalcell.t;
      }
        -> 'mode head
    (* A constant also stores a dimension that it is substituted to and a neutral insertion applied to it.  Many constants are zero-dimensional, meaning that 'c' is zero, and hence a=b is just a dimension and the insertion is trivial.  The dimension of a constant is its dimension as a term standing on its own; so in particular if it has any parameters, then it belongs to an ordinary, 0-dimensional, pi-type and therefore is 0-dimensional, even if the eventual codomain of the pi-type is higher-dimensional.  Note also that when nonidentity insertions end up getting stored here, e.g. by Act, the dimension 'c gets extended as necessary; so it is always okay to create a constant with the (0,0,0) insertion to start with, even if you don't know what its actual dimension is. *)
    | Const : { name : Constant.t; ins : ('a, 'b, 'c) insertion } -> 'mode head
    (* A metavariable (i.e. flexible) head stores the metavariable along with a delayed substitution applied to it. *)
    | Meta : {
        meta : ('mode, 'a, 'b, 's) Meta.t;
        env : ('mode, 'm, 'b) env;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> 'mode head
    (* Universes are parametrized by a mode and a dimension. *)
    | UU : 'mode Mode.t * 'n D.t -> 'mode head
    (* Pis must store not just the domain type but all its boundary types.  These domain and boundary types are not fully instantiated.  Note the codomains are stored in a cube of binders. *)
    | Pi : ('dom, 'modality, 'mode, 'n, 'm) pi_args -> 'mode head

  (* The head of a neutral is either an ordinary head, which can have an application spine, or Failed, which can't. *)
  and (_, _) neu_head =
    (* A failed term, i.e. one that failed to typecheck.  Its value raises a dependent error whenever it is forced, so that anything that needs to inspect it fails silently.  A failed value is unequal to every other value, including other failed values, since it doesn't remember the environment it would have been evaluated in; only physical equality makes it equal to itself. *)
    | Failed : 'mode Mode.t -> ('mode, failed) neu_head
    | Live : 'mode head -> ('mode, live) neu_head

  and ('dom, 'modality, 'mode, 'n, 'm) pi_args = {
    x : 'n variables;
    filter : ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim;
    doms : ('n, ('dom, kinetic) value) CubeOf.t;
    cods : ('m, 'mode * 'modality * 'dom) BindCube.t;
  }

  (* An application contains the data of an n-dimensional argument and its boundary, together with a neutral insertion applied outside that can't be pushed in.  This represents the *argument list* of a single application, not the function.  Thus, an application spine will be a head together with a list of apps.  Each application could be along a different modality. *)
  and (_, _, _, _) apps =
    (* An apps has *two* mode parameters: the first is the mode at the head end of the spine, and the second is the mode of the whole spine.  These differ exactly when the spine crosses a modal field projection, whose left adjoint modality is stored in the Field entry. *)
    | Emp : ('mode, 'mode, noninst, 'fail) apps
    (* m is the dimension of the function being applied, n is the dimension of the arguments *)
    | Arg :
        ('hmode, 'mode, 'any, live) apps
        * ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim
        * ('n, 'dom normal) CubeOf.t
        * ('mk, 'm, 'k) insertion
        -> ('hmode, 'mode, noninst, live) apps
    (* For a higher field with ('n, 't, 'i) insertion, the actual evaluation dimension is 'n, but the result dimension is only 't.  So the dimension of the arg is 't, since that's the output dimension that a degeneracy acting on could be pushed through.  However, since a degeneracy of dimension up to 'n can act on the inside, we can push in the whole insertion and store only a plus outside.  The stored filter_dim is by the left adjoint of the field's adjunction: the spine inside lives at its source mode (behind a lock by it), and at the *filtered* dimension 'ft of the (outer) result dimension 't.  These differ when the field's modality is nonparametric and a degeneracy has acted, filtering some directions of 't away from the projected term; a fresh projection always has a trivial filter with 'ft = 't. *)
    | Field :
        ('hmode, 'src, 'any, live) apps
        * ('src, 'f, 'mode, 'ft, 't) Modality.filter_dim
        * 'i Field.t
        * ('t, 'i, 'n) D.plus
        * ('tk, 't, 'k) insertion
        -> ('hmode, 'mode, noninst, live) apps
    (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial in dimensions, so it should not be applied more than once in a row.  So the dummy parameter of 'apps' tracks whether the last application was an instantiation, and here we verify that it wasn't before instantiating.  We also allow only nontrivial instantiations, to avoid cluttering up application spines with lots of empty instantiations and simplify equality-checking. *)
    | Inst :
        ('hmode, 'mode, noninst, live) apps * 'k D.pos * ('n, 'k, 'nk, 'mode normal) TubeOf.t
        -> ('hmode, 'mode, inst, live) apps

  (* Lambdas and Pis both bind a variable, along with its dependencies.  These are recorded as defunctionalized closures.  Since they are produced by higher-dimensional substitutions and operator actions, the dimension of the binder can be different than the dimension of the environment that closes its body.  Accordingly, in addition to the environment and degeneracy to close its body, we store information about how to map the eventual arguments into the bound variables in the body; this is the insertion.  *)
  and (_, _, _, _, _) binder =
    | Bind : {
        env : ('mode, 'm, 'a) env;
        modality : ('dom, 'modality, 'mode) Modality.t;
        filter : ('dom, 'modality, 'mode, 'l, 'n) Modality.filter_dim;
        body : ('mode, ('a, ('modality, 'l) dim_entry) snoc, 's) term;
        ins : ('mn, 'm, 'n) insertion;
      }
        -> ('mode, 'modality, 'dom, 'mn, 's) binder

  and (_, _) value =
    (* A neutral is an application spine: a head with a list of applications.  It also stores its type, and (lazily) the up-to-now result of evaluating that application spine.  The type is also lazy because the 0-dimensional universe is morally an infinite data structure Uninst (UU 0, (Uninst (UU 0, Uninst (UU 0, ... )))).  If that result is "Unrealized", then it is a "true neutral", the sort of neutral that is permanently stuck and usually appears in paper proofs of normalization.  If it is "Val" then the spine is still waiting for further arguments for its case tree to compute.  If it is "Realized" then the case tree has already evaluated to an ordinary value.  This is how glued evaluation remembers both the neutral and its unfolding. *)
    | Neu : {
        (* The head lives at the mode at the head end of the spine, which differs from the mode of the whole neutral if the spine crosses a modal field projection. *)
        head : ('hmode, 'fail) neu_head;
        args : ('hmode, 'mode, 'any, 'fail) apps;
        value : ('mode, potential) lazy_eval;
        ty : ('mode, kinetic) value Lazy.t;
      }
        -> ('mode, kinetic) value
    (* A constructor has a name, a dimension, and a list of arguments of that dimension.  It must always be applied to the correct number of arguments (otherwise it can be eta-expanded).  It doesn't have an outer insertion because a primitive datatype is always 0-dimensional (it has higher-dimensional versions, but degeneracies can always be pushed inside these).  *)
    | Constr :
        Constr.t * 'n D.t * ('n, 'mode, kinetic) modal_value_cube list
        -> ('mode, kinetic) value
    | Lam :
        'k variables
        * ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
        * ('mode, 'modality, 'dom, 'n, 's) binder
        -> ('mode, 's) value
    (* Structs have to store an insertion outside, like an application, to deal with higher-dimensional record types like Gel.  Here 'k is the Gel dimension, with 'p the substitution dimension and 'pk the total dimension. *)
    | Struct : ('mode, 'p, 'k, 'pk, 's, 'et) struct_args -> ('mode, 's) value
    (* A canonical type is only a *potential* value, so it appears as the 'value' of a 'neu'.  It may also be instantiated, partially or fully. *)
    | Canonical : ('mode, 'm, 'k, 'mk, 'e, 'n) inst_canonical -> ('mode, potential) value

  and ('mode, 'p, 'k, 'pk, 's, 'et) struct_args = {
    fields : ('mode * 'p * 's * 'et) StructfieldAbwd.t;
    ins : ('pk, 'p, 'k) insertion;
    energy : 's energy;
    eta : ('s, 'et) eta;
  }

  and ('mode, 'm, 'k, 'mk, 'e, 'n) inst_canonical = {
    mode : 'mode Mode.t;
    canonical : ('mode, 'e, 'n) canonical;
    (* An insertion that combines its intrinsic dimension n (such as for Gel) with the dimension e it was evaluated at, producing a total dimension mk. *)
    ins : ('mk, 'e, 'n) insertion;
    (* Instantiation arguments for that total dimension. *)
    tyargs : ('m, 'k, 'mk, 'mode normal) TubeOf.t;
    (* Original fibrancy fields for the total dimension, and computed fibrancy fields for the remaining uninstantiated dimensions. *)
    fields : ('mode * 'mk * potential * no_eta) StructfieldAbwd.t;
    mutable inst_fields : ('mode * 'm * potential * no_eta) StructfieldAbwd.t option;
  }

  (* This is the result of evaluating a term with a given kind of energy.  Evaluating a kinetic term just produces a (kinetic) value, whereas evaluating a potential term might be a potential value (either a lambda waiting for more arguments, a struct waiting for more fields, or a canonical type partially or fully instantiated), or else the information that the case tree has reached a leaf and the resulting kinetic value, or else the information that the case tree is permanently stuck.  *)
  and (_, _) evaluation =
    (* When 's = potential, a Val means the case tree is not yet fully applied; while when 's = kinetic, it is the only possible kind of result.  Collapsing these two together seems to unify the code for Lam and Struct as much as possible. *)
    | Val : ('mode, 's) value -> ('mode, 's) evaluation
    | Realize : ('mode, kinetic) value -> ('mode, potential) evaluation
    | Unrealized : ('mode, potential) evaluation

  (* A canonical type value is either a universe, a function-type, a datatype, or a codatatype/record.  It is parametrized by its dimension as a type, which might be larger than its evaluation dimension if it has an intrinsic dimension (e.g. Gel), and by that intrinsic dimension. *)
  and (_, _, _) canonical =
    (* At present, we never produce these except as the values of their corresponding heads.  But in principle, we could allow universes and pi-types as potential terms, so that constants could be defined to "behave like" universes or pi-types without reducing to them. *)
    | UU : 'mode Mode.t * 'm D.t -> ('mode, 'm, D.zero) canonical
    | Pi : ('dom, 'modality, 'mode, 'n, 'm) pi_args -> ('mode, 'm, D.zero) canonical
    (* We define a named record type to encapsulate the arguments of Data and Codata, rather than using an inline one, so that we can bind their existential variables (https://discuss.ocaml.org/t/annotating-by-an-existential-type/14721).  See the definitions of these records below. *)
    | Data : ('mode, 'm, 'j, 'ij) data_args -> ('mode, 'm, D.zero) canonical
    | Codata : ('mode, 'm, 'n, 'a, 'et) codata_args -> ('mode, 'm, 'n) canonical

  (* A datatype value stores: *)
  and ('mode, 'm, 'j, 'ij) data_args = {
    (* The dimension to which it is substituted *)
    dim : 'm D.t;
    (* The datatype family after being applied to the parameters but not the indices, e.g. "Vec A", together with its type.  Computed lazily at evaluation time by evaluating the [tyfam] term stored in the corresponding [Term.Data] (read back when the datatype was checked) and reading its type off the resulting neutral; see the comment there. *)
    tyfam : ('mode, kinetic) lazy_eval;
    (* The indices applied so far, and the number remaining *)
    indices : (('m, 'mode normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    (* All the constructors *)
    constrs : (Constr.t, ('mode, 'm) dataconstr) Abwd.t;
    (* Whether it has recursive constructors. *)
    recursive : Positivity.recursion;
    (* Variable-name hints, for displaying anonymous variables of this type. *)
    hints : hints;
  }

  (* A codatatype stores: *)
  and ('mode, 'm, 'n, 'a, 'et) codata_args = {
    (* An eta flag and an opacity *)
    eta : (potential, 'et) eta;
    opacity : opacity;
    (* Variable-name hints, for displaying anonymous variables of this type. *)
    hints : hints;
    (* The environment that it was evaluated in *)
    env : ('mode, 'm, 'a) env;
    (* Its fields, as unevaluted terms that depend on one additional variable belonging to the codatatype itself (usually through its previous fields).  They are the fields as typechecked, hence of evaluation dimension zero: the evaluation dimension 'm of the value is applied by tyof_codatafield when a field is projected, not stored in the fields themselves.  Note that combining env, ins, and any of the field terms in a *lower* codatafield produces the data of a binder; so in the absence of higher codatatypes we can think of this as a family of binders, one for each field, that share the same environment and insertion.  (But with higher fields this is no longer the case, as the context of the types gets degenerated by their dimension.) *)
    fields : ('mode * 'a * D.zero * 'n * 'et) Term.CodatafieldAbwd.t;
  }

  (* Each constructor stores its function-type (the iterated pi-type over its argument telescope with the datatype applied to the parameters and indices as codomain) as a closure over the datatype's environment.  It is walked on demand — e.g. by ext_pi in match typechecking — evaluating and introducing the arguments to reach the output type, whose trailing arguments are the index values. *)
  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('mode, 'm, 'a) env;
        ty : ('mode, 'a, kinetic) term;
        (* The function-type evaluated in env, computed lazily and cached, so that all the constructor applications checked, compared, or read back at one datatype value share a single evaluation of it.  It is acted on along with env. *)
        fnty : ('mode, kinetic) lazy_eval;
      }
        -> ('mode, 'm) dataconstr

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and 'mode normal = { tm : ('mode, kinetic) value; ty : ('mode, kinetic) value Lazy.t }

  (* The binding of one variable in an environment; see Ext below. *)
  and ('mk, 'dom) env_binding =
    [ `Lazy of ('mk, ('dom, kinetic) lazy_eval) CubeOf.t
    | `Ok of ('mk, ('dom, kinetic) value) CubeOf.t ]

  (* An "environment" is a context morphism *from* a De Bruijn LEVEL context *to* a (typechecked) De Bruijn INDEX context.  Specifically, an ('n, 'a) env is an 'n-dimensional substitution from a level context to an index context indexed by the hctx 'a.  Since the index context could have some variables that are labeled by integers together with faces, the values also have to allow that.  The environment is NOT parametrized by a mode: the terms in it could belong to many modes, namely the domains of the modality annotations in the codomain context.  We don't enforce the validity of those modes here. *)
  and (_, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'n, 'mode emp) env
    (* The (n+k)-cube here is morally a k-cube of n-cubes, representing a k-dimensional "cube variable" consisting of some number of "real" variables indexed by the faces of a k-cube, each of which has an n-cube of values representing a value and its boundaries.  But this contains the same data as an (n+k)-cube since a strict face of (n+k) decomposes uniquely as a strict face of n plus a strict face of k, and it seems to be more convenient to store it as a single (n+k)-cube. *)
    | Ext : {
        env : ('mode, 'n, 'b) env;
        plus : ('m, 'k, 'mk) D.plus;
        filter : ('dom, 'modality, 'mode, 'm, 'n) Modality.filter_dim;
        filtered : ('dom, 'modality, 'mode, 'k, 'k) Modality.filter_dim;
        (* We have two kinds of variable bindings in an environment: lazy and non-lazy.   We also allow Error binding in an environment, indicating that that variable is not actually usable, usually due to an earlier error in typechecking that we've continued on from anyway.  (There's no need for errors in the lazy case, since the lazy thunk can just raise an error directly when forced.) *)
        values : ('mk, 'dom) env_binding;
      }
        -> ('mode, 'n, ('b, ('modality, 'k) dim_entry) snoc) env
    | Act : ('mode, 'n, 'b) env * ('m, 'n) opt_op -> ('mode, 'm, 'b) env
    (* A Lock is the lift of a substitution to a context extended by a lock for one generating modality, paralleling Ctx.Ordered.Lock and the lock entries of a Tctx.  It changes the mode of the environment from the generator's target to its source.  A more general key, which semantically precomposes a lock by a 2-cell, is represented by a Prekey on top of one or more Locks. *)
    | Lock :
        ('cod, 'n, 'b) env * ('dom, 'g, 'cod) Modality.gen
        -> ('dom, 'n, ('b, 'g lock_entry) snoc) env
    (* A Prekey lazily acts by a key cell on all the values in an environment, without changing its mode or codomain context.  Semantically, it is precomposition of the substitution with a key substitution.  This is how a key acts on the captured environment of a closure: variables bound by the closure itself (added on top of the Prekey) are not affected. *)
    | Prekey : ('mode, 'n, 'b) env * ('mode, 'mu, 'nu, 'cod) Modalcell.t -> ('mode, 'n, 'b) env
    | Permute : ('a, 'b) permute * ('mode, 'n, 'b) env -> ('mode, 'n, 'a) env
    (* Adding a dimension 'n to all the dimensions in a dimension list 'b is the power/cotensor in the dimension-enriched category of contexts.  Shifting an environment (substitution) implements its universal property: an (m+n)-dimensional substitution with codomain b is equivalent to an m-dimensional substitution with codomain n+b. *)
    | Shift :
        ('mode, 'mn, 'b) env * ('m, 'n, 'mn) D.plus * ('n, 'b, 'nb, 'mode) plusmap
        -> ('mode, 'm, 'nb) env
    (* Unshifting is the inverse operation, which semantically is composing with the universal n-dimensional substitution from n+b to b. *)
    | Unshift :
        ('mode, 'm, 'nb) env * ('m, 'n, 'mn) D.plus * ('n, 'b, 'nb, 'mode) plusmap
        -> ('mode, 'mn, 'b) env

  (* An 's lazy_eval behaves from the outside like an 's evaluation Lazy.t.  But internally, in addition to being able to store an arbitrary thunk, it can also store a term and an environment in which to evaluate it (plus an outer insertion and key that can't be pushed into the environment).  This allows it to accept degeneracy actions and incorporate them into the environment, so that when it's eventually forced the term only has to be traversed once.  Finally, it can store a pending application or action applied to another lazy_eval: this is how glued evaluation defers the computation of an application spine.  Since the inner lazy_eval is shared rather than copied, forcing either one caches its result for the other, so that a prefix of a spine that is forced on its own (e.g. the value of a partial application f x, when f x y is also forced) is evaluated only once. *)
  and ('mode, 's) lazy_state =
    | Deferred_eval :
        ('mode, 'm, 'b) env
        * ('mode, 'b, 's) term
        * ('mn, 'm, 'n) insertion
        * ('mode, 'mu, 'nu, 'cod) Modalcell.t
        -> ('mode, 's) lazy_state
    | Deferred : (unit -> ('mode, 's) evaluation) -> ('mode, 's) lazy_state
    | Applied : ('hmode, 's) lazy_eval * ('hmode, 'mode) lazy_app -> ('mode, 's) lazy_state
    | Ready : ('mode, 's) evaluation -> ('mode, 's) lazy_state

  and ('mode, 's) lazy_eval = ('mode, 's) lazy_state ref

  and (_, _) lazy_app =
    | Apps : ('hmode, 'mode, 'any, live) apps -> ('hmode, 'mode) lazy_app
    | Action : ('m, 'n) deg * ('mode, 'mu, 'nu, 'cod) Modalcell.t -> ('mode, 'mode) lazy_app
end

include Value

(* Any neutral is automatically a normal. *)
let nf_of_neu : type mode. (mode, kinetic) value -> string -> mode normal =
 fun tm str ->
  match tm with
  | Neu { ty; _ } -> { tm; ty }
  | _ -> fatal (Anomaly ("nf_of_neu: " ^ str))

type (_, _) modal_value =
  | Modal : ('dom, 'modality, 'mode) Modality.t * ('dom, 's) value -> ('mode, 's) modal_value

type any_canonical = Any : ('mode, 'm, 'n) canonical -> any_canonical

(* Every context morphism has a valid dimension. *)
let rec dim_env : type mode n b. (mode, n, b) env -> n D.t = function
  | Emp (_, n) -> n
  | Ext { env; _ } -> dim_env env
  | Act (_, op) -> dom_opt_op op
  | Lock (e, _) -> dim_env e
  | Prekey (e, _) -> dim_env e
  | Permute (_, e) -> dim_env e
  | Shift (e, mn, _) -> D.plus_left mn (dim_env e)
  | Unshift (e, mn, _) -> D.plus_out (dim_env e) mn

(* And likewise every binder *)
let dim_binder : type mode modality dom m s. (mode, modality, dom, m, s) binder -> m D.t =
 fun (Bind b) -> dom_ins b.ins

let modality_binder : type mode modality dom m s.
    (mode, modality, dom, m, s) binder -> (dom, modality, mode) Modality.t =
 fun (Bind b) -> b.modality

let rec mode_env : type mode n b. (mode, n, b) env -> mode Mode.t = function
  | Emp (mode, _) -> mode
  | Ext { env; _ } -> mode_env env
  | Act (e, _) -> mode_env e
  | Lock (_, g) -> Modality.Gen.src g
  | Prekey (e, _) -> mode_env e
  | Permute (_, e) -> mode_env e
  | Shift (e, _, _) -> mode_env e
  | Unshift (e, _, _) -> mode_env e

(* let dim_canonical : type mode m n mn. (mode, m, n, mn) canonical -> mn D.t = function
     | UU dim -> dim
     | Pi (_, doms, _) -> CubeOf.dim doms
     | Data { dim; _ } -> dim
     | Codata { ins; _ } -> dom_ins ins *)

(* The length of an environment is a tctx. *)
let rec length_env : type mode n b. (mode, n, b) env -> (mode, b) Tctx.t = function
  | Emp (mode, _) -> Tctx.emp mode
  | Ext { env; plus; filtered; _ } ->
      let le = length_env env in
      Tctx.suc le (Dim (D.plus_right plus, filtered))
  | Act (env, _) -> length_env env
  | Lock (env, g) -> Tctx.suc (length_env env) (Lock g)
  | Prekey (env, _) -> length_env env
  | Permute (p, env) -> perm_dom p (length_env env)
  | Shift (_, mn, nb) -> Plusmap.cod (D.plus_right mn) nb
  | Unshift (_, _, nb) -> Plusmap.dom nb

(* Smart constructor that composes actions and cancels identities *)
let rec act_env : type mode m n b. (mode, n, b) env -> (m, n) opt_op -> (mode, m, b) env =
 fun env s ->
  match env with
  | Act (env, s') -> act_env env (comp_opt_op s' s)
  | _ -> (
      match is_id_opt_op s with
      | Some Eq -> env
      | None -> Act (env, s))

(* Lock an environment by a modality, one generator at a time, mirroring how the type-level context (Tctx) breaks a lock into its generators. *)
let rec lock_env : type dom mu cod m b bmu.
    (cod, m, b) env -> (b, cod, mu, dom, bmu) plus_lock -> (dom, m, bmu) env =
 fun env plus ->
  match plus with
  | Plus_lock (Zero _, Zero) -> env
  | Plus_lock (Suc (lock, Inject (Lock_lock g), Suc (Zero, Lock _)), Suc (comp, Lock g')) ->
      (* The Lock.t and the comp are indexed by separate existentials for the intermediate object left after peeling off the outer generator; reconcile them through the shared generator, as Ordered.lock_to does. *)
      let Eq = Modality.Gen.src_uniq g g' in
      let Eq = Modality.Gen.tgt_uniq g g' in
      Lock (lock_env env (Plus_lock (lock, comp)), g)

(* For prekeys, all a smart constructor can do is ignore identities (on any modality). *)
let prekey_env : type mode mu nu cod n b.
    (mode, n, b) env -> (mode, mu, nu, cod) Modalcell.t -> (mode, n, b) env =
 fun env key -> if Modalcell.is_id key then env else Prekey (env, key)

(* Remove the top entry from an environment.  Looks through lazy operations like Act, Prekey, Shift, Unshift, and Permute.  No Locks are allowed to the right of the entry: this is ensured by the type, since an insert only passes dimension entries. *)
let remove_top : type mode a modality k n.
    (mode, n, (a, (modality, k) dim_entry) snoc) env -> (mode, n, a) env =
 fun env ->
  (* Because of the possibility of permutations, the recursion has to allow for the possibility of non-top elements. *)
  let rec remove_ins : type mode modality a k b n.
      (mode, n, b) env -> (a, modality, k, b) insert -> (mode, n, a) env =
   fun env v ->
    match (env, v) with
    | Emp _, _ -> .
    | Act (env, op), _ -> Act (remove_ins env v, op)
    | Lock _, _ -> .
    | Prekey (env, key), _ -> Prekey (remove_ins env v, key)
    | Permute (p, env), _ ->
        let (Permute_insert (v', p')) = permute_insert v p in
        Permute (p', remove_ins env v')
    | Ext e, Later v -> Ext { e with env = remove_ins e.env v }
    | Ext { env; _ }, Now -> env
    | Shift (env, mn, nb), _ ->
        let (Uncoinsert (_, _, v', na)) = Plusmap.uncoinsert v nb in
        Shift (remove_ins env v', mn, na)
    | Unshift (env, mn, nb), _ ->
        let (Uninsert (_, _, v', na)) = Plusmap.uninsert v nb in
        Unshift (remove_ins env v', mn, na) in
  remove_ins env Now

(* A prekey action is a key cell with a given mode as vertical source but existential vertical target (and horizontal target). *)
type _ prekey_action = Prekey_action : ('mode, 'm, 'n, 'cod) Modalcell.t -> 'mode prekey_action

(* Prewhisker a prekey action by a modality, transporting its vertical (and horizontal) source. *)
let prekey_prewhisker : type mode a b m n r.
    (mode, m, n, b) Modalcell.t -> (a, r, mode) Modality.t -> a prekey_action =
 fun pre mu ->
  let (Wrap pre) = Modalcell.prewhisker_wrapped pre mu in
  Prekey_action pre

(* Compose a prekey cell after an accumulated prekey action, both sharing the environment's mode as vertical source.  This is the general composition of key cells (as in act.ml's key_vcomp), using a pushout to reconcile the accumulated action's vertical target with the new prekey's vertical source. *)
let prekey_vcomp : type mode m n cod pm pn pcod.
    (mode, m, n, cod) Modalcell.t -> (mode, pm, pn, pcod) Modalcell.t -> mode prekey_action =
 fun key pre ->
  match Modality.pushout (Modalcell.vtgt pre) (Modalcell.vsrc key) with
  | Some (Pushout (mu3, mu4, cod13, dom24)) ->
      let (Comp cod24) = Modality.comp (Modalcell.vtgt key) in
      let (Comp dom13) = Modality.comp (Modalcell.vsrc pre) in
      Prekey_action
        (Modalcell.vcomp
           (Modalcell.hcomp dom24 cod24 (Modalcell.id mu4) key)
           (Modalcell.hcomp dom13 cod13 (Modalcell.id mu3) pre))
  | None -> fatal (Anomaly "prekey_vcomp: prekeys don't compose")

(* Given an environment whose codomain context is extended by a partial context containing some locks (and dimensions), strip off the Locks in the environment corresponding to those locks, and return the remainder of the environment along with a "prekey action" composed from all the Prekeys encountered along the way.  Since Locks carry no cells, any key action is represented by a Prekey; these act on a looked-up value at the environment's mode with a vertical target that may differ from the composite of the stripped locks, so they are accumulated separately and applied to the value at the end.  The prekeys accumulated inside a Lock act at its inner mode, so to carry them outward we prewhisker them by the lock's generator.  When no (nonidentity) prekeys are encountered, the returned cell is id2, and hence dropped by the smart constructor prekey_env.  Thus the input environment is semantically equal to the residual one, locked by the extension and then prekeyed by the returned cell. *)
type (_, _, _, _) restrict_keys =
  | Restrict_keys :
      ('cod, 'k, 'b) env * ('mode, 'pmu, 'pnu, 'pcod) Modalcell.t
      -> ('mode, 'cod, 'k, 'b) restrict_keys

let rec restrict_keys : type mode mu cod k b bc.
    (mode, k, bc) env -> (b, cod, mu, mode, bc) plus_with_locks -> (mode, cod, k, b) restrict_keys =
 fun env (Plus_with_locks (bc, llc)) ->
  match (bc, llc, env) with
  (* If we're out of locks to strip off, we bottom out the recursion, returning an identity prekey cell. *)
  | Zero, Zero _, _ -> Restrict_keys (env, Modalcell.id2 (mode_env env))
  (* If we encounter a Lock, it must match the outermost lock in the extension, which we consume. *)
  | Suc (bc, Lock g0), Suc (llc, Locks_lock g', Suc (Zero, _)), Lock (env, g) ->
      let Eq = Modality.Gen.src_uniq g0 g' in
      let Eq = Modality.Gen.tgt_uniq g0 g' in
      let Eq = Modality.Gen.src_uniq g g' in
      let Eq = Modality.Gen.tgt_uniq g g' in
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (bc, llc)) in
      let (Prekey_action pre) = prekey_prewhisker pre (Modality.of_gen g) in
      Restrict_keys (env, pre)
  (* If we encounter a dimension entry, we skip it. *)
  | Suc (bc, Dim _), Suc (llc, Locks_dim _, Zero), _ ->
      restrict_keys (remove_top env) (Plus_with_locks (bc, llc))
  (* A Proj is not possible due to the typing of contexts. *)
  | Suc (_, Proj _), Suc (_, _, _), _ -> .
  (* If we have more locks to strip off, but we find a prekey on the environment, that doesn't correspond to any locks in the codomain context, so we accumulate it into the prekey-action cell, which shares the environment's (unchanging) mode, composing it after any inner prekeys with the general key-cell composition.  Note that the extension could be exhausted here: we continue accumulating prekeys until we run out of ones that we *could* include. *)
  | (Suc _ as bc), llc, Prekey (env, key) ->
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (bc, llc)) in
      let (Prekey_action pre) = prekey_vcomp key pre in
      Restrict_keys (env, pre)
  (* If we encounter some other operation that could still have further locks inside it, we look through it. *)
  | Suc _, _, Permute (p, env) -> (
      match unpermute_plus_locks p bc llc with
      | Some (Unpermute (p, ad, lld)) ->
          let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (ad, lld)) in
          Restrict_keys (Permute (p, env), pre)
      | None ->
          (* This isn't ruled out: the permutation could mix the two parts of the decomposition.  We trust the caller to maintain the invariant. *)
          fatal (Anomaly "restrict_keys: unpermute failure"))
  | (Suc _ as nb_nc), ll_nc, Shift (env, mn, nbc) ->
      let n = D.plus_right mn in
      let (Dom_uncomp (nb, nc, b_c)) = Plusmap.dom_uncomp n nb_nc nbc in
      let (Eq _) = Plusmap.tgt nc in
      let ll_c = Plusmap.unlocks nc ll_nc in
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (b_c, ll_c)) in
      Restrict_keys (Shift (env, mn, nb), pre)
  | (Suc _ as b_c), ll_c, Unshift (env, mn, nbc) ->
      let n = D.plus_right mn in
      let (Uncomp (nb, nc, nb_nc)) = Plusmap.uncomp n b_c nbc in
      let (Eq _) = Plusmap.tgt nc in
      let ll_nc = Plusmap.locks n nc ll_c in
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (nb_nc, ll_nc)) in
      Restrict_keys (Unshift (env, mn, nb), pre)
  | Suc _, _, Act (env, op) ->
      let (Restrict_keys (env, pre)) = restrict_keys env (Plus_with_locks (bc, llc)) in
      Restrict_keys (Act (env, op), pre)

(* Create a lazy evaluation *)
let lazy_eval : type mode n b s. (mode, n, b) env -> (mode, b, s) term -> (mode, s) lazy_eval =
 fun env tm -> ref (Deferred_eval (env, tm, ins_zero (dim_env env), Modalcell.id2 (mode_env env)))

let defer : type mode s. (unit -> (mode, s) evaluation) -> (mode, s) lazy_eval =
 fun tm -> ref (Deferred tm)

let ready : type mode s. (mode, s) evaluation -> (mode, s) lazy_eval = fun ev -> ref (Ready ev)

let apply_lazy : type dom modality mode m n s.
    (mode, s) lazy_eval ->
    m D.t ->
    (dom, modality, mode, n, m) Modality.filter_dim ->
    (n, dom normal) CubeOf.t ->
    (mode, s) lazy_eval =
 fun lev m filter xs ->
  match !lev with
  | Ready Unrealized -> lev
  | _ -> ref (Applied (lev, Apps (Arg (Emp, filter, xs, ins_zero m))))

(* We defer "field_lazy" to act.ml, since it requires pushing a permutation inside the apps. *)

(* Given a mode, a De Bruijn level, and a type, build the variable of that mode and level having that type. *)
let var : type dom modality mode.
    (dom, modality, mode) Modality.t -> level -> (dom, kinetic) value -> (dom, kinetic) value =
 fun modality level ty ->
  Neu
    {
      head = Live (Var { level; deg = id_deg D.zero; key = Modalcell.id modality });
      args = Emp;
      value = ready Unrealized;
      ty = Lazy.from_val ty;
    }

(* Project out a cube or tube of values from a cube or tube of normals *)
let val_of_norm_cube : type mode n. (n, mode normal) CubeOf.t -> (n, (mode, kinetic) value) CubeOf.t
    =
 fun arg -> CubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

let val_of_norm_tube : type mode n k nk.
    (n, k, nk, mode normal) TubeOf.t -> (n, k, nk, (mode, kinetic) value) TubeOf.t =
 fun arg -> TubeOf.mmap { map = (fun _ [ { tm; ty = _ } ] -> tm) } [ arg ]

(* Binders are completely lazy, so we can "evaluate" them independently of the master evaluation functions in norm. *)
let eval_binder : type mode modality dom m k n mn b s.
    (mode, m, b) env ->
    (m, n, mn) D.plus ->
    (dom, modality, mode) Modality.t ->
    (dom, modality, mode, k, n) Modality.filter_dim ->
    (mode, (b, (modality, k) dim_entry) snoc, s) term ->
    (mode, modality, dom, mn, s) Value.binder =
 fun env mn modality filter body ->
  let m = dim_env env in
  let ins = id_ins m mn in
  Value.Bind { env; modality; filter; ins; body }

(* Same with structfields *)
let rec eval_structfield : type mode m n mn a status i et.
    (mode, m, a) env ->
    m D.t ->
    (m, n, mn) D.plus ->
    mn D.t ->
    (i, mode * (n * a * status * et)) Term.Structfield.t ->
    (i, mode * mn * status * et) Value.Structfield.t =
 fun env m m_n mn fld ->
  match fld with
  | Lower (adj, plus_lock, tm, lbl) ->
      (* The term of a modal field lives behind a lock by the right adjoint, so we evaluate it in the environment keyed (by identity cells, per generator) by the right adjoint. *)
      Lower (adj, lazy_eval (lock_env env plus_lock) tm, lbl)
  | Higher (adj, plus_lock, terms) ->
      (* Like a lower modal field, the terms of a higher modal field live behind a lock by the right adjoint, so we lock the environment by it before storing. *)
      Higher (lazy (eval_higher_structfield adj (lock_env env plus_lock) m m_n mn terms))
  | LazyHigher (adj, plus_lock, terms) ->
      Higher
        (lazy (eval_higher_structfield adj (lock_env env plus_lock) m m_n mn (Lazy.force terms)))

and eval_higher_structfield : type mode f g gmode m n mn ag i.
    (mode, f, g, gmode) Modalcell.adjunction ->
    (gmode, m, ag) env ->
    m D.t ->
    (m, n, mn) D.plus ->
    mn D.t ->
    (n, i, gmode * ag) PlusPbijmap.t ->
    (mode, f, g, gmode, m, n, mn, mn, i, ag) Structfield.higher_data =
 fun adj env m m_n mn terms ->
  let intrinsic = PlusPbijmap.intrinsic terms in
  let vals =
    InsmapOf.build mn intrinsic
      {
        build =
          (fun (type olds) (ins : (mn, olds, i) insertion) ->
            let (Unplus_ins
                   (type news newh t r)
                   ((newins, newshuf, mtr, _ts) :
                     (n, news, newh) insertion
                     * (r, newh, i) shuffle
                     * (m, t, r) insertion
                     * (t, news, olds) D.plus)) =
              unplus_ins m m_n ins in
            let newpbij = Pbij (newins, newshuf) in
            match PlusPbijmap.find newpbij terms with
            | None -> None
            | Some (PlusFam (ra, tm)) ->
                let (Plus tr) = D.plus (cod_right_ins mtr) in
                (* mtrp : m ≅ t+r *)
                let mtrp = deg_of_perm (perm_inv (perm_of_ins_plus mtr tr)) in
                (* env2 is (t+r)-dimensional *)
                let env2 = act_env env (opt_op_of_deg mtrp) in
                (* env3 is t-dimensional *)
                let env3 = Shift (env2, tr, ra) in
                (* We don't need to further permute the result, as all the information about the permutation ins was captured in newpbij and mtr. *)
                Some (lazy_eval env3 tm));
      } in
  { adj; intrinsic; plusdim = m_n; terms; env; deg = id_deg mn; vals }

let eval_structfield_abwd : type mode m n mn a status et.
    (mode, m, a) env ->
    m D.t ->
    (m, n, mn) D.plus ->
    mn D.t ->
    (mode * (n * a * status * et)) Term.StructfieldAbwd.t ->
    (mode * mn * status * et) Value.StructfieldAbwd.t =
 fun env m m_n mn fields ->
  Mbwd.mmap
    (fun [ Term.StructfieldAbwd.Entry (f, sf) ] ->
      Value.StructfieldAbwd.Entry (f, eval_structfield env m m_n mn sf))
    [ fields ]

(* The universe of any dimension belongs to an instantiation of itself.  Note that the result is not itself a type (i.e. in the 0-dimensional universe) unless n=0.  This is the universe itself as a term. *)
(* Since the universe of a given mode and dimension depends on nothing else (Fibrancy.universe is fixed at startup), we memoize it. *)
type cached_universe =
  | Cached_universe : 'mode Mode.t * 'n D.t * ('mode, kinetic) value -> cached_universe

let universe_cache : cached_universe list ref = ref []

let rec universe : type mode n. mode Mode.t -> n D.t -> (mode, kinetic) value =
 fun mode n ->
  let found =
    List.find_map
      (fun (Cached_universe (mode', n', v)) ->
        match (Mode.compare mode' mode, D.compare n' n) with
        | Eq, Eq -> Some (v : (mode, kinetic) value)
        | _ -> None)
      !universe_cache in
  match found with
  | Some v -> v
  | None ->
      let fields =
        match Lazy.force (Fibrancy.universe mode) with
        | None -> Bwd.Emp
        | Some fields -> eval_structfield_abwd (Emp (mode, n)) n (D.plus_zero n) n fields in
      let value =
        ready
          (Val
             (Canonical
                {
                  mode;
                  canonical = UU (mode, n);
                  tyargs = TubeOf.empty n;
                  ins = ins_zero n;
                  fields;
                  inst_fields = Some fields;
                })) in
      let v =
        Neu { head = Live (UU (mode, n)); args = Emp; value; ty = lazy (universe_ty mode n) } in
      universe_cache := Cached_universe (mode, n, v) :: !universe_cache;
      v

and universe_nf : type mode n. mode Mode.t -> n D.t -> mode normal =
 fun mode n -> { tm = universe mode n; ty = lazy (universe_ty mode n) }

(* And this is the instantiation of itself that it belongs to.  This is a type (i.e. an element of the 0-dimensional universe), so it must be fully instantiated.  *)
and universe_ty : type mode n. mode Mode.t -> n D.t -> (mode, kinetic) value =
 fun mode n ->
  match D.compare_zero n with
  | Zero -> universe mode D.zero
  | Pos n' ->
      let args =
        TubeOf.build D.zero (D.zero_plus n)
          {
            build =
              (fun fa ->
                let m = dom_tface fa in
                universe_nf mode m);
          } in
      let fields =
        match Lazy.force (Fibrancy.universe mode) with
        | None -> Bwd.Emp
        | Some fields -> eval_structfield_abwd (Emp (mode, n)) n (D.plus_zero n) n fields in
      let value =
        ready
          (Val
             (Canonical
                {
                  mode;
                  canonical = UU (mode, n);
                  tyargs = args;
                  ins = ins_zero n;
                  fields;
                  inst_fields = None;
                })) in
      Neu
        {
          head = Live (UU (mode, n));
          args = Inst (Emp, n', args);
          value;
          ty = lazy (universe mode D.zero);
        }

(* A failed term with a given type (see Failed above).  Each call creates a new value. *)
let failed : type mode. mode Mode.t -> (mode, kinetic) value Lazy.t -> (mode, kinetic) value =
 fun mode ty ->
  Neu
    {
      head = Failed mode;
      args = Emp;
      value = defer (fun () -> fatal (Dependent "failed term"));
      ty;
    }

(* A failed type, i.e. a failed term whose type is the universe.  This is also the type of a failed term whose type is unknown. *)
let failed_type : type mode. mode Mode.t -> (mode, kinetic) value =
 fun mode -> failed mode (lazy (universe mode D.zero))

(* A failed term whose type is unknown, such as the value of a Failed term. *)
let failed_untyped : type mode. mode Mode.t -> (mode, kinetic) value =
 fun mode -> failed mode (lazy (failed_type mode))

type ('hmode, 'mode) any_apps = Any : ('hmode, 'mode, 'any, live) apps -> ('hmode, 'mode) any_apps

(* Instantiate a lazy value.  An instantiation of an Unrealized value is still Unrealized. *)
let inst_lazy : type mode m n mn s.
    (mode, s) lazy_eval -> (m, n, mn, mode normal) TubeOf.t -> (mode, s) lazy_eval =
 fun lev args ->
  match (D.compare_zero (TubeOf.inst args), !lev) with
  | Zero, _ | _, Ready Unrealized -> lev
  | Pos k, _ -> ref (Applied (lev, Apps (Inst (Emp, k, args))))

let inst_tys : ('mode, kinetic) value -> ('mode, kinetic) value TubeOf.full = function
  | Neu { ty = (lazy (Neu { args = Inst (_, _, tys); _ })); _ } -> (
      match D.compare (TubeOf.uninst tys) D.zero with
      | Eq ->
          let Eq = D.plus_uniq (D.zero_plus (TubeOf.inst tys)) (TubeOf.plus tys) in
          Full_tube (val_of_norm_tube tys)
      | Neq -> fatal (Anomaly "universe must be fully instantiated to be a type"))
  (* A term whose type is failed, such as a degeneracy of a failed term whose type is unknown, has no instantiation arguments to read off. *)
  | Neu { ty = (lazy (Neu { head = Failed _; _ })); _ } ->
      fatal (Dependent "instantiating a term of failed type")
  | _ -> fatal (Anomaly "invalid type, has no instantiation arguments")

(* Split off an instantiation, if any, at the end of an apps *)
let inst_of_apps : type hmode mode any.
    (hmode, mode, any, live) apps ->
    (hmode, mode, noninst, live) apps * mode normal TubeOf.any option =
 fun apps ->
  match apps with
  | Inst (base_args, _, args1) -> (base_args, Some (TubeOf.Any_tube args1))
  | Emp -> (apps, None)
  | Arg _ -> (apps, None)
  | Field _ -> (apps, None)

(* A head together with an application spine ending at a given mode, with the mode at the head end existentially quantified. *)
type _ head_apps = Head_apps : 'hmode head * ('hmode, 'mode) any_apps -> 'mode head_apps

(* Split off a given positive dimension's worth of instantiation, putting the rest back on the apps.  The argument must be a neutral, so the return value is just the head and apps part of a neutral (which suffices to read it back with readback_neu). *)
let split_inst : type mode m.
    m D.pos ->
    (mode, kinetic) value ->
    (mode head_apps * (D.zero, m, m, mode normal) TubeOf.t) option =
 fun m tm ->
  let m = D.pos m in
  match tm with
  | Neu { head = Live head; args = Inst (args, mk, tyargs); _ } -> (
      match (D.compare_zero (TubeOf.uninst tyargs), D.factor (D.pos mk) m) with
      | Zero, Some (Factor m_k) -> (
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (D.pos mk)) in
          let tyargs, rest = TubeOf.split (D.zero_plus m) m_k tyargs in
          match D.compare_zero (D.plus_right m_k) with
          | Zero -> Some (Head_apps (head, Any args), tyargs)
          | Pos k -> Some (Head_apps (head, Any (Inst (args, k, rest))), tyargs))
      | _ -> None)
  | _ -> None

module Fwd_app = struct
  (* Make an apps without instantiations into a forwards type-aligned sequence.  A single entry takes a spine ending at its first mode parameter to one ending at its second; the two differ for modal field projections. *)
  type (_, _) t =
    | Arg :
        ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim
        * ('n, 'dom normal) CubeOf.t
        * ('mk, 'm, 'k) insertion
        -> ('mode, 'mode) t
    | Field :
        ('src, 'f, 'mode, 'ft, 't) Modality.filter_dim
        * 'i Field.t
        * ('t, 'i, 'n) D.plus
        * ('tk, 't, 'k) insertion
        -> ('src, 'mode) t

  type (_, _) fwd = Nil : ('mode, 'mode) fwd | Cons : ('a, 'b) t * ('b, 'c) fwd -> ('a, 'c) fwd

  let snoc : type hmode mode mode2 any.
      (hmode, mode, any, live) apps -> (mode, mode2) t -> (hmode, mode2, noninst, live) apps =
   fun apps app ->
    match app with
    | Arg (filter, arg, ins) -> Arg (apps, filter, arg, ins)
    | Field (f, fld, plus, ins) -> Field (apps, f, fld, plus, ins)

  let of_apps : type hmode mode any. (hmode, mode, any, live) apps -> (hmode, mode) fwd =
   fun apps ->
    let rec go : type hmode mode mode2 any.
        (hmode, mode, any, live) apps -> (mode, mode2) fwd -> (hmode, mode2) fwd =
     fun apps fwds ->
      match apps with
      | Emp -> fwds
      | Arg (apps, filter, arg, ins) -> go apps (Cons (Arg (filter, arg, ins), fwds))
      | Field (apps, f, fld, plus, ins) -> go apps (Cons (Field (f, fld, plus, ins), fwds))
      | Inst _ -> fatal (Anomaly "instantiation in fwd_of_apps") in
    go apps Nil
end

(* The result of splitting an application spine ending at a given mode: a prefix spine ending at some intermediate mode, and the rest as a forward sequence. *)
type (_, _) split_apps =
  | Split_apps :
      ('hmode, 'mode2, noninst, live) apps * ('mode2, 'mode) Fwd_app.fwd
      -> ('hmode, 'mode) split_apps

(* Given two apps, the second longer, split the second into one of the same length and the rest. *)
let split_apps_at_length : type hmode1 hmode2 mode1 mode2 any1 any2.
    (hmode1, mode1, any1, live) apps ->
    (hmode2, mode2, any2, live) apps ->
    (hmode2, mode2) split_apps option =
 fun apps1 apps2 ->
  let rec go : type h1 m1 m2 mode2.
      (hmode2, m2, noninst, live) apps ->
      (h1, m1) Fwd_app.fwd ->
      (m2, mode2) Fwd_app.fwd ->
      (hmode2, mode2) split_apps option =
   fun apps2 fwd1 fwd2 ->
    match (fwd1, fwd2) with
    | Nil, _ -> Some (Split_apps (apps2, fwd2))
    | Cons (_, fwd1), Cons (app2, fwd2) -> go (Fwd_app.snoc apps2 app2) fwd1 fwd2
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
