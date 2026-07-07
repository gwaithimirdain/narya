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
          ('mode, 's) Value.lazy_eval * [ `Labeled | `Unlabeled ]
          -> (D.zero, 'mode * 'n * 's * 'et) t
      | Higher :
          ('mode, 'm, 'n, 'mn, 'p, 'i, 'a) higher_data Lazy.t
          -> ('i, 'mode * 'p * potential * no_eta) t

    and ('mode, 'm, 'n, 'mn, 'p, 'i, 'a) higher_data = {
      vals : ('p, 'i, ('mode, potential) Value.lazy_eval option) InsmapOf.t;
      intrinsic : 'i D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      env : ('mode, 'm, 'a) Value.env;
      deg : ('p, 'mn) deg;
      terms : ('n, 'i, 'mode * 'a) PlusPbijmap.t;
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

  and ('dom, 'modality, 'mode, 'n, 'm) pi_args = {
    x : 'n variables;
    filter : ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim;
    doms : ('n, ('dom, kinetic) value) CubeOf.t;
    cods : ('m, 'mode * 'modality * 'dom) BindCube.t;
  }

  and (_, _) apps =
    | Emp : ('mode, noninst) apps
    | Arg :
        ('mode, 'any) apps
        * ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim
        * ('n, 'dom normal) CubeOf.t
        * ('mk, 'm, 'k) insertion
        -> ('mode, noninst) apps
    | Field :
        ('mode, 'any) apps * 'i Field.t * ('t, 'i, 'n) D.plus * ('tk, 't, 'k) insertion
        -> ('mode, noninst) apps
    | Inst :
        ('mode, noninst) apps * 'k D.pos * ('n, 'k, 'nk, 'mode normal) TubeOf.t
        -> ('mode, inst) apps

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
        head : 'mode head;
        args : ('mode, 'any) apps;
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
    | Codata : ('mode, 'm, 'n, 'c, 'a, 'et) codata_args -> ('mode, 'm, 'n) canonical

  and ('mode, 'm, 'j, 'ij) data_args = {
    dim : 'm D.t;
    tyfam : 'mode normal Lazy.t option ref;
    indices : (('m, 'mode normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    constrs : (Constr.t, ('mode, 'm) dataconstr) Abwd.t;
    discrete : [ `Yes | `Maybe | `No ];
    recursive : Positivity.recursion;
    hints : hints;
  }

  and ('mode, 'm, 'n, 'c, 'a, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    hints : hints;
    env : ('mode, 'm, 'a) env;
    termctx : ('mode, 'c, ('a, ('mode id, 'n) dim_entry) snoc) termctx option Lazy.t;
    fields : ('mode * 'a * 'n * 'et) Term.CodatafieldAbwd.t;
  }

  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('mode, 'm, 'a) env;
        args : ('mode, 'a, 'p, 'ap) Telescope.t;
        output : ('mode, 'ap, kinetic) term;
      }
        -> ('mode, 'm) dataconstr

  and 'mode normal = { tm : ('mode, kinetic) value; ty : ('mode, kinetic) value }

  and (_, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'n, 'mode emp) env
    | Ext : {
        env : ('mode, 'n, 'b) env;
        plus : ('m, 'k, 'mk) D.plus;
        filter : ('dom, 'modality, 'mode, 'm, 'n) Modality.filter_dim;
        filtered : ('dom, 'modality, 'mode, 'k, 'k) Modality.filter_dim;
        values :
          [ `Lazy of ('mk, ('dom, kinetic) lazy_eval) CubeOf.t
          | `Ok of ('mk, ('dom, kinetic) value) CubeOf.t
          | `Error of Code.t ];
      }
        -> ('mode, 'n, ('b, ('modality, 'k) dim_entry) snoc) env
    | Act : ('mode, 'n, 'b) env * ('m, 'n) opt_op -> ('mode, 'm, 'b) env
    | Key :
        ('mode, 'n, 'b) env
        * ('dom, 'mu, 'nu, 'mode) Modalcell.t
        * ('b, 'mode, 'mu, 'dom, 'bm) plus_lock
        -> ('dom, 'n, 'bm) env
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
        * ('mode, 'mu, 'nu, 'cod) Modalcell.t option
        * ('mode, 'any) apps
        -> ('mode, 's) lazy_state
    | Deferred :
        (unit -> ('mode, 's) evaluation)
        * ('m, 'n) deg
        * ('mode, 'mu, 'nu, 'cod) Modalcell.t option
        * ('mode, 'any) apps
        -> ('mode, 's) lazy_state
    | Ready : ('mode, 's) evaluation -> ('mode, 's) lazy_state

  and ('mode, 's) lazy_eval = ('mode, 's) lazy_state ref
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
      (* We remember which fields are labeled, for readback purposes, and we store the value of each field lazily, so that corecursive definitions don't try to compute an entire infinite structure.  And since in the non-kinetic case, evaluation can produce more data than just a term (e.g. whether a case tree has yet reached a leaf), what we store lazily is the result of evaluation. *)
      | Lower :
          ('mode, 's) Value.lazy_eval * [ `Labeled | `Unlabeled ]
          -> (D.zero, 'mode * 'n * 's * 'et) t
      (* In the higher case, they are always labeled.  There are multiple values are indexed by insertions, regarded as partial bijections with zero remaining dimensions; the 'evaluation dimension is the substitution dimension 'n and the 'intrinsic dimension is associated to the field.  We also store the original terms as a closure, since they may be needed to evaluate fields of degeneracies. *)
      | Higher :
          ('mode, 'm, 'n, 'mn, 'p, 'i, 'a) higher_data Lazy.t
          -> ('i, 'mode * 'p * potential * no_eta) t

    and ('mode, 'm, 'n, 'mn, 'p, 'i, 'a) higher_data = {
      vals : ('p, 'i, ('mode, potential) Value.lazy_eval option) InsmapOf.t;
      intrinsic : 'i D.t;
      plusdim : ('m, 'n, 'mn) D.plus;
      env : ('mode, 'm, 'a) Value.env;
      deg : ('p, 'mn) deg;
      terms : ('n, 'i, 'mode * 'a) PlusPbijmap.t;
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

  and ('dom, 'modality, 'mode, 'n, 'm) pi_args = {
    x : 'n variables;
    filter : ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim;
    doms : ('n, ('dom, kinetic) value) CubeOf.t;
    cods : ('m, 'mode * 'modality * 'dom) BindCube.t;
  }

  (* An application contains the data of an n-dimensional argument and its boundary, together with a neutral insertion applied outside that can't be pushed in.  This represents the *argument list* of a single application, not the function.  Thus, an application spine will be a head together with a list of apps.  Each application could be along a different modality. *)
  and (_, _) apps =
    | Emp : ('mode, noninst) apps
    (* m is the dimension of the function being applied, n is the dimension of the arguments *)
    | Arg :
        ('mode, 'any) apps
        * ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim
        * ('n, 'dom normal) CubeOf.t
        * ('mk, 'm, 'k) insertion
        -> ('mode, noninst) apps
    (* For a higher field with ('n, 't, 'i) insertion, the actual evaluation dimension is 'n, but the result dimension is only 't.  So the dimension of the arg is 't, since that's the output dimension that a degeneracy acting on could be pushed through.  However, since a degeneracy of dimension up to 'n can act on the inside, we can push in the whole insertion and store only a plus outside. *)
    | Field :
        ('mode, 'any) apps * 'i Field.t * ('t, 'i, 'n) D.plus * ('tk, 't, 'k) insertion
        -> ('mode, noninst) apps
    (* An (m+n)-dimensional type is "instantiated" by applying it a "boundary tube" to get an m-dimensional type.  This operation is supposed to be functorial in dimensions, so it should not be applied more than once in a row.  So the dummy parameter of 'apps' tracks whether the last application was an instantiation, and here we verify that it wasn't before instantiating.  We also allow only nontrivial instantiations, to avoid cluttering up application spines with lots of empty instantiations and simplify equality-checking. *)
    | Inst :
        ('mode, noninst) apps * 'k D.pos * ('n, 'k, 'nk, 'mode normal) TubeOf.t
        -> ('mode, inst) apps

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
    (* A neutral is an application spine: a head with a list of applications.  It also stores its type, and (lazily) the up-to-now result of evaluating that application spine.  The type is also lazy because the 0-dimensional universe is morally an infinite data structure Uninst (UU 0, (Uninst (UU 0, Uninst (UU 0, ... )))).  If that result is "Unrealized", then it is a "true neutral", the sort of neutral that is permanently stuck and usually appears in paper proofs of normalization.  If it is "Val" then the spine is still waiting for further arguments for its case tree to compute.  If it is "Realized" then the case tree has already evaluated to an ordinary value; this should only happen when glued evaluation is in effect. *)
    | Neu : {
        head : 'mode head;
        args : ('mode, 'any) apps;
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
    | Codata : ('mode, 'm, 'n, 'c, 'a, 'et) codata_args -> ('mode, 'm, 'n) canonical

  (* A datatype value stores: *)
  and ('mode, 'm, 'j, 'ij) data_args = {
    (* The dimension to which it is substituted *)
    dim : 'm D.t;
    (* The datatype family after being applied to the parameters but not the indices, e.g. "Vec A".  This is an option ref because it gets set a little later than the rest of the fields are computed, since only when working with the embedding of neutrals into normals do we have the application spine and its type available.  *)
    tyfam : 'mode normal Lazy.t option ref;
    (* The indices applied so far, and the number remaining *)
    indices : (('m, 'mode normal) CubeOf.t, 'j, 'ij) Fillvec.t;
    (* All the constructors *)
    constrs : (Constr.t, ('mode, 'm) dataconstr) Abwd.t;
    (* Whether it is discrete.  The value `Maybe means that it could be discrete based on its own parameters, indices, and constructor arguments, but either is waiting for its mutual companions to be typechecked, or at least one of them failed to be discrete.  Thus for equality-testing purposes, `Maybe is treated like `No. *)
    discrete : [ `Yes | `Maybe | `No ];
    (* Whether it has recursive constructors. *)
    recursive : Positivity.recursion;
    (* Variable-name hints, for displaying anonymous variables of this type. *)
    hints : hints;
  }

  (* A codatatype stores: *)
  and ('mode, 'm, 'n, 'c, 'a, 'et) codata_args = {
    (* An eta flag and an opacity *)
    eta : (potential, 'et) eta;
    opacity : opacity;
    (* Variable-name hints, for displaying anonymous variables of this type. *)
    hints : hints;
    (* The environment and termctx that it was evaluated in *)
    env : ('mode, 'm, 'a) env;
    termctx : ('mode, 'c, ('a, ('mode id, 'n) dim_entry) snoc) termctx option Lazy.t;
    (* Its fields, as unevaluted terms that depend on one additional variable belonging to the codatatype itself (usually through its previous fields).  Note that combining env, ins, and any of the field terms in a *lower* codatafield produces the data of a binder; so in the absence of higher codatatypes we can think of this as a family of binders, one for each field, that share the same environment and insertion.  (But with higher fields this is no longer the case, as the context of the types gets degenerated by their dimension.) *)
    fields : ('mode * 'a * 'n * 'et) Term.CodatafieldAbwd.t;
  }

  (* Each constructor stores the telescope of types of its arguments, as a closure, and its output type (the datatype applied to the parameters and indices); the index values are the trailing arguments of the output, extracted on demand. *)
  and (_, _) dataconstr =
    | Dataconstr : {
        env : ('mode, 'm, 'a) env;
        args : ('mode, 'a, 'p, 'ap) Telescope.t;
        output : ('mode, 'ap, kinetic) term;
      }
        -> ('mode, 'm) dataconstr

  (* A "normal form" is a value paired with its type.  The type is used for eta-expansion and equality-checking. *)
  and 'mode normal = { tm : ('mode, kinetic) value; ty : ('mode, kinetic) value }

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
        values :
          [ `Lazy of ('mk, ('dom, kinetic) lazy_eval) CubeOf.t
          | `Ok of ('mk, ('dom, kinetic) value) CubeOf.t
          | `Error of Code.t ];
      }
        -> ('mode, 'n, ('b, ('modality, 'k) dim_entry) snoc) env
    | Act : ('mode, 'n, 'b) env * ('m, 'n) opt_op -> ('mode, 'm, 'b) env
    | Key :
        ('mode, 'n, 'b) env
        * ('dom, 'mu, 'nu, 'mode) Modalcell.t
        * ('b, 'mode, 'mu, 'dom, 'bm) plus_lock
        -> ('dom, 'n, 'bm) env
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

  (* An 's lazy_eval behaves from the outside like an 's evaluation Lazy.t.  But internally, in addition to being able to store an arbitrary thunk, it can also store a term and an environment in which to evaluate it (plus an outer insertion that can't be pushed into the environment).  This allows it to accept degeneracy actions and incorporate them into the environment, so that when it's eventually forced the term only has to be traversed once.  It can also accumulate degeneracies on an arbitrary thunk (which could, of course, be a constant value that was already forced, but now is deferred again until it's done accumulating degeneracy actions).  Both kinds of deferred values can also store more arguments and field projections for it to be applied to; this is only used in glued evaluation. *)
  and ('mode, 's) lazy_state =
    | Deferred_eval :
        ('mode, 'm, 'b) env
        * ('mode, 'b, 's) term
        * ('mn, 'm, 'n) insertion
        * ('mode, 'mu, 'nu, 'cod) Modalcell.t option
        * ('mode, 'any) apps
        -> ('mode, 's) lazy_state
    | Deferred :
        (unit -> ('mode, 's) evaluation)
        * ('m, 'n) deg
        * ('mode, 'mu, 'nu, 'cod) Modalcell.t option
        * ('mode, 'any) apps
        -> ('mode, 's) lazy_state
    | Ready : ('mode, 's) evaluation -> ('mode, 's) lazy_state

  and ('mode, 's) lazy_eval = ('mode, 's) lazy_state ref
end

include Value

type (_, _) modal_value =
  | Modal : ('dom, 'modality, 'mode) Modality.t * ('dom, 's) value -> ('mode, 's) modal_value

type any_canonical = Any : ('mode, 'm, 'n) canonical -> any_canonical

(* Every context morphism has a valid dimension. *)
let rec dim_env : type mode n b. (mode, n, b) env -> n D.t = function
  | Emp (_, n) -> n
  | Ext { env; _ } -> dim_env env
  | Act (_, op) -> dom_opt_op op
  | Key (e, _, _) -> dim_env e
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
  | Key (_, key, _) -> Modalcell.hsrc key
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
  | Key (env, _, al) -> plus_lock_out (length_env env) al
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

(* There is very little possibility of a "smart constructor" for keys since we track their domains in the length type parameter; all we can do is ignore identities. *)
let key_env : type dom mu nu cod m b bmu.
    (cod, m, b) env ->
    (dom, mu, nu, cod) Modalcell.t ->
    (b, cod, mu, dom, bmu) plus_lock ->
    (dom, m, bmu) env =
 fun env key al ->
  match (Modalcell.compare_id key, al) with
  | Eq, Plus_lock (Zero _, Zero) -> env
  | _ -> Key (env, key, al)

(* Similarly, for prekeys all we can do is ignore identities. *)
let prekey_env : type mode mu nu cod n b.
    (mode, n, b) env -> (mode, mu, nu, cod) Modalcell.t -> (mode, n, b) env =
 fun env key ->
  match Modalcell.compare_id key with
  | Eq -> env
  | Neq -> Prekey (env, key)

(* Remove the top entry from an environment.  Looks through lazy operations like Act, Prekey, Shift, Unshift, and Permute.  No Keys are allowed to the right of the entry: this is (almost) ensured by the type, since its codomain context ends with a lock. *)
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
    | Key _, _ -> fatal (Anomaly "Key in remove_ins")
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

(* Given an environment whose codomain context is extended by a partial context containing some locks (and dimensions), split off all the keys corresponding to those locks, compose them up on the way out, and return them along with the remainder of the environment.  This is the incremental version of the operation that lookup uses to key on a variable; the prekeys and (post)keys are composed on the way out rather than being stripped off eagerly at the beginning.  Identity-domain keys and prekeys are always accumulated into the returned cell. *)

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
  | None -> fatal (Anomaly "restrict_keys: prekeys don't compose")

(* In addition to the residual environment and the composite key cell (which maps the looked-up value's own annotating modality, at the environment's mode, to the base after stripping the locks), we return a "prekey action" cell.  Prekeys act on the looked-up value at the environment's mode with a possibly-different vertical target than the composite locks, so they can't be folded into the same cell; instead we compose them separately (into this second cell) and apply them to the value after the composite key cell.  When no prekeys are encountered, this cell is an identity, and hence dropped by the smart constructor prekey_env. *)
type (_, _, _, _, _) restrict_keys =
  | Restrict_keys :
      ('cod, 'n, 'b) env
      * ('mode, 'mu, 'nu, 'cod) Modalcell.t
      * ('mode, 'pmu, 'pnu, 'pcod) Modalcell.t
      -> ('mode, 'mu, 'cod, 'n, 'b) restrict_keys

let rec restrict_keys : type mode mu cod k b bc.
    (mode, k, bc) env ->
    (b, cod, mu, mode, bc) plus_with_locks ->
    (mode, mu, cod, k, b) restrict_keys =
 fun env (Plus_with_locks (bc, llc)) ->
  match (bc, llc, env) with
  (* If we encounter a key, we accumulate it, consuming the corresponding locks from the codomain-context extension.  Note that the extension could be identity here: we continue accumulating keys until we run out of keys that we *could* include, not just until we run out of nonidentity locks in the codomain. *)
  | b_cn, llcn, Key (env, key, Plus_lock (ln, bc_n)) -> (
      let lln = locks_lock ln in
      let cn, n = (Locks.dom llcn, Lock.cod ln) in
      match Tctx.factor cn n with
      | None ->
          (* The type of this function doesn't rule this out: the decomposition of the length of the environment could land in the middle of the domain of a key.  We have to trust the caller to maintain the invariant. *)
          fatal (Anomaly "restrict_keys: factor failure")
      | Some (Factor (_c, c_n)) ->
          let (Uncomp (llc, lln', m_n)) = Locks.uncomp c_n llcn in
          let Eq = Locks.uniq lln lln' in
          let b_c = Tctx.comp_assoc_cancelr c_n b_cn bc_n in
          let (Restrict_keys (e, keys, pre)) = restrict_keys env (Plus_with_locks (b_c, llc)) in
          (* A key changes the mode: the prekey action accumulated inside it acts at the inner mode, so to carry it outward we prewhisker it by the key's vertical target, transporting its source to the outer mode. *)
          let (Prekey_action pre) = prekey_prewhisker pre (Modalcell.vtgt key) in
          let (Comp nus) = Modality.comp (Modalcell.vtgt key) in
          Restrict_keys (e, Modalcell.hcomp m_n nus keys key, pre))
  (* A prekey doesn't correspond to any locks in the codomain context, and its cell may have a different vertical target than the composite keys of the actual variable's locks (which is fixed by the codomain-context extension), so we can't fold it into that cell.  Instead we accumulate it into the separate prekey-action cell, which shares the environment's (unchanging) mode, composing it after any inner prekeys with the general key-cell composition. *)
  | bc, llc, Prekey (env, key) ->
      let (Restrict_keys (env, keys, pre)) = restrict_keys env (Plus_with_locks (bc, llc)) in
      let (Prekey_action pre) = prekey_vcomp key pre in
      Restrict_keys (env, keys, pre)
  (* If we encounter a dimension entry, we skip it. *)
  | Suc (bc, Dim _), Suc (llc, Locks_dim _, Zero), _ ->
      restrict_keys (remove_top env) (Plus_with_locks (bc, llc))
  (* If we encounter some other operation that could still have further keys inside it, we look through it. *)
  | _, _, Permute (p, env) -> (
      match unpermute_plus_locks p bc llc with
      | Some (Unpermute (p, ad, lld)) ->
          let (Restrict_keys (env, keys, pre)) = restrict_keys env (Plus_with_locks (ad, lld)) in
          Restrict_keys (Permute (p, env), keys, pre)
      | None ->
          (* This isn't ruled out either: the permutation could mix the two parts of the decomposition.  Again, we trust the caller to maintain the invariant. *)
          fatal (Anomaly "restrict_keys: unpermute failure"))
  | nb_nc, ll_nc, Shift (env, mn, nbc) ->
      let n = D.plus_right mn in
      let (Dom_uncomp (nb, nc, b_c)) = Plusmap.dom_uncomp n nb_nc nbc in
      let (Eq _) = Plusmap.tgt nc in
      let ll_c = Plusmap.unlocks nc ll_nc in
      let (Restrict_keys (env, keys, pre)) = restrict_keys env (Plus_with_locks (b_c, ll_c)) in
      Restrict_keys (Shift (env, mn, nb), keys, pre)
  | b_c, ll_c, Unshift (env, mn, nbc) ->
      let n = D.plus_right mn in
      let (Uncomp (nb, nc, nb_nc)) = Plusmap.uncomp n b_c nbc in
      let (Eq _) = Plusmap.tgt nc in
      let ll_nc = Plusmap.locks n nc ll_c in
      let (Restrict_keys (env, keys, pre)) = restrict_keys env (Plus_with_locks (nb_nc, ll_nc)) in
      Restrict_keys (Unshift (env, mn, nb), keys, pre)
  | _, _, Act (env, op) ->
      let (Restrict_keys (env, keys, pre)) = restrict_keys env (Plus_with_locks (bc, llc)) in
      Restrict_keys (Act (env, op), keys, pre)
  (* If we reach the end of the environment, or a value entry, we bottom out the recursion, returning identity key and prekey cells. *)
  | Zero, Zero _, Emp _ ->
      Restrict_keys (env, Modalcell.id2 (mode_env env), Modalcell.id2 (mode_env env))
  | Zero, Zero _, Ext _ ->
      Restrict_keys (env, Modalcell.id2 (mode_env env), Modalcell.id2 (mode_env env))
  (* Nothing else is possible, since if the tctx has a nonzero lock on it, the environment can't be empty or end with a value entry. *)
  | Suc (_, Lock _), Suc (_, Locks_lock _, Suc (_, _)), _ -> .
  | Suc (_, Proj _), Suc (_, _, _), _ -> .

let restrict_keys_plus_lock : type mode mu cod k b bm.
    (mode, k, bm) env -> (b, cod, mu, mode, bm) plus_lock -> (mode, mu, cod, k, b) restrict_keys =
 fun env plus -> restrict_keys env (plus_with_locks_of_plus_lock plus)

(* Create a lazy evaluation *)
let lazy_eval : type mode n b s. (mode, n, b) env -> (mode, b, s) term -> (mode, s) lazy_eval =
 fun env tm -> ref (Deferred_eval (env, tm, ins_zero (dim_env env), None, Emp))

let defer : type mode s. (unit -> (mode, s) evaluation) -> (mode, s) lazy_eval =
 fun tm -> ref (Deferred (tm, id_deg D.zero, None, Emp))

let ready : type mode s. (mode, s) evaluation -> (mode, s) lazy_eval = fun ev -> ref (Ready ev)

let apply_lazy : type dom modality mode m n s.
    (mode, s) lazy_eval ->
    m D.t ->
    (dom, modality, mode, n, m) Modality.filter_dim ->
    (n, dom normal) CubeOf.t ->
    (mode, s) lazy_eval =
 fun lev m filter xs ->
  let xins = ins_zero m in
  match !lev with
  | Deferred_eval (env, tm, ins, cell, apps) ->
      ref (Deferred_eval (env, tm, ins, cell, Arg (apps, filter, xs, xins)))
  | Deferred (tm, ins, cell, apps) -> ref (Deferred (tm, ins, cell, Arg (apps, filter, xs, xins)))
  | Ready tm -> ref (Deferred ((fun () -> tm), id_deg D.zero, None, Arg (Emp, filter, xs, xins)))

(* We defer "field_lazy" to act.ml, since it requires pushing a permutation inside the apps. *)

(* Given a mode, a De Bruijn level, and a type, build the variable of that mode and level having that type. *)
let var : type dom modality mode.
    (dom, modality, mode) Modality.t -> level -> (dom, kinetic) value -> (dom, kinetic) value =
 fun modality level ty ->
  Neu
    {
      head = Var { level; deg = id_deg D.zero; key = Modalcell.id modality };
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
  | Lower (tm, l) -> Lower (lazy_eval env tm, l)
  | Higher terms -> Higher (lazy (eval_higher_structfield env m m_n mn terms))
  | LazyHigher terms -> Higher (lazy (eval_higher_structfield env m m_n mn (Lazy.force terms)))

and eval_higher_structfield : type mode m n mn a i.
    (mode, m, a) env ->
    m D.t ->
    (m, n, mn) D.plus ->
    mn D.t ->
    (n, i, mode * a) PlusPbijmap.t ->
    (mode, m, n, mn, mn, i, a) Structfield.higher_data =
 fun env m m_n mn terms ->
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
  { intrinsic; plusdim = m_n; terms; env; deg = id_deg mn; vals }

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
let rec universe : type mode n. mode Mode.t -> n D.t -> (mode, kinetic) value =
 fun mode n ->
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
  Neu { head = UU (mode, n); args = Emp; value; ty = lazy (universe_ty mode n) }

and universe_nf : type mode n. mode Mode.t -> n D.t -> mode normal =
 fun mode n -> { tm = universe mode n; ty = universe_ty mode n }

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
          head = UU (mode, n);
          args = Inst (Emp, n', args);
          value;
          ty = lazy (universe mode D.zero);
        }

type 'mode any_apps = Any : ('mode, 'any) apps -> 'mode any_apps

(* Smart constructor that coalesces instantiations *)
let inst_apps : type mode any m n mn.
    (mode, any) apps -> (m, n, mn, mode normal) TubeOf.t -> mode any_apps =
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
let inst_lazy : type mode m n mn s.
    (mode, s) lazy_eval -> (m, n, mn, mode normal) TubeOf.t -> (mode, s) lazy_eval =
 fun lev args ->
  match D.compare_zero (TubeOf.inst args) with
  | Zero -> lev
  | Pos k -> (
      match !lev with
      | Deferred_eval (env, tm, ins, cell, apps) ->
          let (Any newargs) = inst_apps apps args in
          ref (Deferred_eval (env, tm, ins, cell, newargs))
      | Deferred (tm, ins, cell, apps) ->
          let (Any newargs) = inst_apps apps args in
          ref (Deferred (tm, ins, cell, newargs))
      | Ready tm -> ref (Deferred ((fun () -> tm), id_deg D.zero, None, Inst (Emp, k, args))))

let inst_tys : ('mode, kinetic) value -> ('mode, kinetic) value TubeOf.full = function
  | Neu { ty = (lazy (Neu { args = Inst (_, _, tys); _ })); _ } -> (
      match D.compare (TubeOf.uninst tys) D.zero with
      | Eq ->
          let Eq = D.plus_uniq (D.zero_plus (TubeOf.inst tys)) (TubeOf.plus tys) in
          Full_tube (val_of_norm_tube tys)
      | Neq -> fatal (Anomaly "universe must be fully instantiated to be a type"))
  | _ -> fatal (Anomaly "invalid type, has no instantiation arguments")

(* Split off an instantiation, if any, at the end of an apps *)
let inst_of_apps : type mode any.
    (mode, any) apps -> (mode, noninst) apps * mode normal TubeOf.any option =
 fun apps ->
  match apps with
  | Inst (base_args, _, args1) -> (base_args, Some (TubeOf.Any_tube args1))
  | Emp -> (apps, None)
  | Arg _ -> (apps, None)
  | Field _ -> (apps, None)

(* Split off a given positive dimension's worth of instantiation, putting the rest back on the apps.  The argument must be a neutral, so the return value is just the head and apps part of a neutral (which suffices to read it back with readback_neu). *)
let split_inst : type mode m.
    m D.pos ->
    (mode, kinetic) value ->
    (mode head * mode any_apps * (D.zero, m, m, mode normal) TubeOf.t) option =
 fun m tm ->
  let m = D.pos m in
  match tm with
  | Neu { head; args = Inst (args, mk, tyargs); _ } -> (
      match (D.compare_zero (TubeOf.uninst tyargs), D.factor (D.pos mk) m) with
      | Zero, Some (Factor m_k) -> (
          let Eq = D.plus_uniq (TubeOf.plus tyargs) (D.zero_plus (D.pos mk)) in
          let tyargs, rest = TubeOf.split (D.zero_plus m) m_k tyargs in
          match D.compare_zero (D.plus_right m_k) with
          | Zero -> Some (head, Any args, tyargs)
          | Pos k -> Some (head, Any (Inst (args, k, rest)), tyargs))
      | _ -> None)
  | _ -> None

module Fwd_app = struct
  (* Make an apps without instantiations into a forwards list *)
  type 'mode t =
    | Arg :
        ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim
        * ('n, 'dom normal) CubeOf.t
        * ('mk, 'm, 'k) insertion
        -> 'mode t
    | Field : 'i Field.t * ('t, 'i, 'n) D.plus * ('tk, 't, 'k) insertion -> 'mode t

  let snoc : type mode any. (mode, any) apps -> mode t -> (mode, noninst) apps =
   fun apps app ->
    match app with
    | Arg (filter, arg, ins) -> Arg (apps, filter, arg, ins)
    | Field (fld, plus, ins) -> Field (apps, fld, plus, ins)

  let of_apps apps =
    let rec go : type mode any. (mode, any) apps -> mode t list -> mode t list =
     fun apps fwds ->
      match apps with
      | Emp -> fwds
      | Arg (apps, filter, arg, ins) -> go apps (Arg (filter, arg, ins) :: fwds)
      | Field (apps, fld, plus, ins) -> go apps (Field (fld, plus, ins) :: fwds)
      | Inst _ -> fatal (Anomaly "instantiation in fwd_of_apps") in
    go apps []
end

(* Given two apps, the second longer, split the second into one of the same length and the rest. *)
let split_apps_at_length : type mode any1 any2.
    (mode, any1) apps -> (mode, any2) apps -> ((mode, noninst) apps * mode Fwd_app.t list) option =
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
