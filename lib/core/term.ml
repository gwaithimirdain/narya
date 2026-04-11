open Bwd
open Util
open Modal
open Tbwd
open Dim
open Dimbwd
include Variables
include Energy

type (_, _, _) is_glue =
  | Glue :
      (Hott.dim, ((((emp, D.zero) snoc, D.zero) snoc, D.zero) snoc, D.zero) snoc, has_eta) is_glue

(* ******************** Typechecked terms ******************** *)

(* Typechecked, but unevaluated, terms.  Use De Bruijn indices that are intrinsically well-scoped by hctxs, but are no longer separated into synthesizing and checking; hence without type ascriptions.  Note that extending an hctx by a dimension 'k means adding a whole cube of new variables, which are indexed by the position of that dimension together with a strict face of it.  (At user-level, those variables may all be accessed as faces of one "cube variable", or they may have independent names, but internally there is no difference.)

   Incorporates information appropriate to the internal syntax that is constructed during typechecking, e.g. applications and abstractions are grouped by a dimension, since this can be inferred during typechecking, from the synthesized type of a function being applied and from the pi-type the lambda is being checked against, respectively.  Similarly, we have instantiations of higher-dimensional types obtained by applying them to a tube of boundary terms.

   Typechecking of user syntax still produces only unary pi-types and zero-dimensional universes, but we include arbitrary-dimensional ones here so that they can also be the output of readback from internal values.  We likewise include arbitrary degeneracy actions, since these can appear in readback. *)

(* The codomain of a higher-dimensional pi-type is a cube of terms with bound variables whose number varies with the face of the cube.  We can enforce this with a parametrized instance of Cube, but it has to be defined recursively with term using a recursive module (like BindCube in Value; see there for more commentary).  Since term now has three type parameters ('mode, 'a, 's) but Cube requires a Fam2 with two parameters, we pack 'mode * 'a into the second parameter of CodFam using a GADT constructor. *)
module rec Term : sig
  module CodFam : sig
    type ('k, _) t = Cod : ('mode, ('a, 'k) snoc, kinetic) Term.term -> ('k, 'mode * 'a) t
  end

  module CodCube : module type of Cube (CodFam)

  module PlusFam : sig
    type (_, _) some =
      | PlusFam :
          (('r, 'b, 'rb) Plusmap.t * ('mode, 'rb, potential) Term.term)
          -> ('r, 'mode * 'b) some

    type ('r, 'mb) t = ('r, 'mb) some option
  end

  module PlusPbijmap : module type of Pbijmap (PlusFam)

  module Codatafield : sig
    type (_, _) t =
      | Lower : ('mode, ('a, 'n) snoc, kinetic) Term.term -> (D.zero, 'mode * 'a * 'n * 'et) t
      | Higher :
          ('i, ('a, D.zero) snoc, 'ian) Plusmap.t * ('mode, 'ian, kinetic) Term.term
          -> ('i, 'mode * 'a * D.zero * no_eta) t
  end

  module CodatafieldAbwd : module type of Field.Abwd (Codatafield)

  module Structfield : sig
    type (_, _) t =
      | Lower :
          ('mode, 'a, 's) Term.term * [ `Labeled | `Unlabeled ]
          -> (D.zero, 'mode * ('n * 'a * 's * 'et)) t
      | Higher :
          ('n, 'i, 'mode * 'a) PlusPbijmap.t
          -> ('i, 'mode * ('n * 'a * potential * no_eta)) t
      | LazyHigher :
          ('n, 'i, 'mode * 'a) PlusPbijmap.t Lazy.t
          -> ('i, 'mode * ('n * 'a * potential * no_eta)) t
  end

  module StructfieldAbwd : module type of Field.Abwd (Structfield)

  module TermFam : sig
    type ('mode, 'a, 's) t = ('mode, 'a, 's) Term.term
  end

  module ModalTermCube : module type of Modality.Cube (TermFam)

  type _ index = Index : ('a, 'n, 'b) Tbwd.insert * ('k, 'n) sface -> 'b index

  type (_, _, _) term =
    | Var : 'a index -> ('mode, 'a, kinetic) term
    | Const : Constant.t -> ('mode, 'a, kinetic) term
    | Meta : ('mode, 'x, 'b, 'l) Meta.t * 's energy -> ('mode, 'b, 's) term
    | MetaEnv : ('mode, 'x, 'b, 's) Meta.t * ('mode, 'a, 'n, 'b) env -> ('mode, 'a, kinetic) term
    | Field :
        ('mode, 'a, kinetic) term * 'i Field.t * ('n, 't, 'i) insertion
        -> ('mode, 'a, kinetic) term
    | UU : 'mode Mode.t * 'n D.t -> ('mode, 'a, kinetic) term
    | Inst :
        ('mode, 'a, kinetic) term * ('m, 'n, 'mn, ('mode, 'a, kinetic) term) TubeOf.t
        -> ('mode, 'a, kinetic) term
    | Pi :
        'n variables
        * ('dom, 'modality, 'mode) Modality.t
        * ('n, ('dom, 'a, kinetic) term) CubeOf.t
        * ('n, 'mode * 'a) CodCube.t
        -> ('mode, 'a, kinetic) term
    | App :
        ('mode, 'a, kinetic) term
        * ('dom, 'modality, 'mode) Modality.t
        * ('n, ('dom, 'a, kinetic) term) CubeOf.t
        -> ('mode, 'a, kinetic) term
    | Constr :
        Constr.t * 'n D.t * ('n, 'mode, 'a, kinetic) ModalTermCube.t list
        -> ('mode, 'a, kinetic) term
    | Act :
        ('mode, 'a, kinetic) term
        * ('m, 'n) deg
        * ([ `Type | `Function | `Other ] * [ `Canonical | `Other ])
        -> ('mode, 'a, kinetic) term
    | Key :
        ('mode, 'a, kinetic) term * ('a, 'c, 'ac) Tbwd.append * ('mode, 'mu, 'nu, 'cod) Modalcell.t
        -> ('mode, 'ac, kinetic) term
    | Let :
        string option
        * ('dom, 'modality, 'mode) Modality.t
        * ('dom, 'a, kinetic) term
        * ('mode, ('a, D.zero) snoc, 's) term
        -> ('mode, 'a, 's) term
    | Lam : 'n variables * ('mode, ('a, 'n) snoc, 's) Term.term -> ('mode, 'a, 's) term
    | Struct : ('mode, 'n, 'a, 's, 'et) struct_args -> ('mode, 'a, 's) term
    | Match : {
        tm : ('mode, 'a, kinetic) term;
        dim : 'n D.t;
        branches : ('mode, 'a, 'n) branch Constr.Map.t;
      }
        -> ('mode, 'a, potential) term
    | Realize : ('mode, 'a, kinetic) term -> ('mode, 'a, potential) term
    | Canonical : ('mode, 'a) canonical -> ('mode, 'a, potential) term
    | Unshift : 'n D.t * ('n, 'b, 'nb) Plusmap.t * ('mode, 'nb, 's) term -> ('mode, 'b, 's) term
    | Unact : ('m, 'n) op * ('mode, 'b, 's) term -> ('mode, 'b, 's) term
    | Shift : 'n D.t * ('n, 'b, 'nb) Plusmap.t * ('mode, 'b, 's) term -> ('mode, 'nb, 's) term
    | Weaken : ('mode, 'b, 's) term -> ('mode, ('b, 'n) snoc, 's) term

  and ('mode, 'n, 'a, 's, 'et) struct_args = {
    dim : 'n D.t;
    fields : ('mode * ('n * 'a * 's * 'et)) StructfieldAbwd.t;
    eta : ('s, 'et) eta;
    energy : 's energy;
  }

  and (_, _, _) branch =
    | Branch :
        ('a, 'b, 'n, 'ab) Tbwd.snocs * ('c, 'ab) Tbwd.permute * ('mode, 'c, potential) term
        -> ('mode, 'a, 'n) branch
    | Refute

  and (_, _) canonical =
    | Data : {
        indices : 'i Fwn.t;
        constrs : (Constr.t, ('mode, 'a, 'i) dataconstr) Abwd.t;
        discrete : [ `Yes | `Maybe | `No ];
      }
        -> ('mode, 'a) canonical
    | Codata : ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et) codata_args -> ('mode, 'a) canonical

  and ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    dim : 'n D.t;
    termctx : ('mode, 'c, ('a, 'n) snoc) termctx option;
    fields : ('mode * 'a * 'n * 'et) CodatafieldAbwd.t;
    fibrancy : ('mode, 'n, 'n, 'nh, 'a, 'ha, 'et) codata_fibrancy;
    is_glue : ('n, 'a, 'et) is_glue option;
  }

  and ('mode, 'g, 'n, 'nh, 'b, 'hb, 'et) codata_fibrancy = {
    glue : 'g D.t;
    dim : 'n D.t;
    length : 'b Plusmap.OfDom.t;
    plusmap : (Hott.dim, 'b, 'hb) Plusmap.t;
    eta : (potential, 'et) eta;
    ty : ('mode, 'b, kinetic) term;
    dimh : ('n, Hott.dim, 'nh) D.plus;
    trr : ('mode * ('n * ('hb, D.zero) snoc * potential * 'et)) StructfieldAbwd.t;
    trl : ('mode * ('n * ('hb, D.zero) snoc * potential * 'et)) StructfieldAbwd.t;
    liftr : ('mode * ('nh * ('hb, D.zero) snoc * potential * 'et)) StructfieldAbwd.t;
    liftl : ('mode * ('nh * ('hb, D.zero) snoc * potential * 'et)) StructfieldAbwd.t;
  }

  and (_, _, _) dataconstr =
    | Dataconstr : {
        args : ('mode, 'p, 'a, 'pa) tel;
        indices : (('mode, 'pa, kinetic) term, 'i) Vec.t;
      }
        -> ('mode, 'p, 'i) dataconstr

  and ('mode, 'a, 'b, 'ab) tel =
    | Emp : ('mode, 'a, Fwn.zero, 'a) tel
    | Ext :
        string option
        * ('dom, 'modality, 'mode) Modality.t
        * ('dom, 'a, kinetic) term
        * ('mode, ('a, D.zero) snoc, 'b, 'ab) tel
        -> ('mode, 'a, 'b Fwn.suc, 'ab) tel

  and (_, _, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'a, 'n, emp) env
    | Ext :
        ('mode, 'a, 'n, 'b) env
        * ('n, 'k, 'nk) D.plus
        * ('dom, 'modality, 'mode) Modality.t
        * ('nk, ('dom, 'a, kinetic) term) CubeOf.t
        -> ('mode, 'a, 'n, ('b, 'k) snoc) env
    | Key :
        ('mode, 'a, 'n, 'b) env * ('a, 'c, 'ac) Tbwd.append * ('dom, 'mu, 'nu, 'mode) Modalcell.t
        -> ('dom, 'ac, 'n, 'b) env

  and ('mode, 'b) binding = {
    ty : ('mode, 'b, kinetic) term;
    tm : ('mode, 'b, kinetic) term option;
  }

  and (_, _) has_fields =
    | No_fields : ('m, N.zero) has_fields
    | Has_fields : (D.zero, 'f2) has_fields

  and (_, _, _, _, _, _) entry =
    | Vis : {
        dim : 'm D.t;
        modality : ('dom, 'modality, 'mode) Modality.t;
        plusdim : ('m, 'n, 'mn) D.plus;
        vars : (N.zero, 'n, string option, 'f1) NICubeOf.t;
        bindings : ('mn, ('dom, ('b, 'mn) snoc) binding) CubeOf.t;
        hasfields : ('m, 'f2) has_fields;
        fields : (D.zero Field.t * string * ('dom, ('b, 'mn) snoc, kinetic) term, 'f2) Bwv.t;
        fplus : ('f1, 'f2, 'f) N.plus;
      }
        -> ('dom, 'modality, 'mode, 'b, 'f, 'mn) entry
    | Invis :
        ('dom, 'modality, 'mode) Modality.t * ('n, ('dom, ('b, 'n) snoc) binding) CubeOf.t
        -> ('dom, 'modality, 'mode, 'b, N.zero, 'n) entry

  and (_, _, _) ordered_termctx =
    | Emp : 'mode Mode.t -> ('mode, N.zero, emp) ordered_termctx
    | Ext :
        ('mode, 'a, 'b) ordered_termctx
        * ('dom, 'modality, 'mode, 'b, 'x, 'n) entry
        * ('a, 'x, 'ax) N.plus
        -> ('mode, 'ax, ('b, 'n) snoc) ordered_termctx
    | Lock :
        ('mode, 'a, 'b) ordered_termctx * ('dom, 'modality, 'mode) Modality.t * bool
        -> ('dom, 'a, 'b) ordered_termctx

  and ('mode, 'a, 'b) termctx =
    | Permute : ('a, 'i) N.perm * ('mode, 'i, 'b) ordered_termctx -> ('mode, 'a, 'b) termctx
end = struct
  module CodFam = struct
    type ('k, _) t = Cod : ('mode, ('a, 'k) snoc, kinetic) Term.term -> ('k, 'mode * 'a) t
  end

  module CodCube = Cube (CodFam)

  module PlusFam = struct
    type (_, _) some =
      | PlusFam :
          (('r, 'b, 'rb) Plusmap.t * ('mode, 'rb, potential) Term.term)
          -> ('r, 'mode * 'b) some

    type ('r, 'mb) t = ('r, 'mb) some option
  end

  module PlusPbijmap = Pbijmap (PlusFam)

  module Codatafield = struct
    type (_, _) t =
      | Lower : ('mode, ('a, 'n) snoc, kinetic) Term.term -> (D.zero, 'mode * 'a * 'n * 'et) t
      | Higher :
          ('i, ('a, D.zero) snoc, 'ian) Plusmap.t * ('mode, 'ian, kinetic) Term.term
          -> ('i, 'mode * 'a * D.zero * no_eta) t
  end

  module CodatafieldAbwd = Field.Abwd (Codatafield)

  module Structfield = struct
    (* Lazy fields are not allowed in ordinary terms, because a term is supposed to be a completed data object that can be, for instance, serialized to a file and reloaded.  But when we use this to store fibrancy fields, which are recomputed on evaluation and are corecursively infinite, we have to allow laziness.  *)
    type (_, _) t =
      | Lower :
          ('mode, 'a, 's) Term.term * [ `Labeled | `Unlabeled ]
          -> (D.zero, 'mode * ('n * 'a * 's * 'et)) t
      | Higher :
          ('n, 'i, 'mode * 'a) PlusPbijmap.t
          -> ('i, 'mode * ('n * 'a * potential * no_eta)) t
      | LazyHigher :
          ('n, 'i, 'mode * 'a) PlusPbijmap.t Lazy.t
          -> ('i, 'mode * ('n * 'a * potential * no_eta)) t
  end

  module StructfieldAbwd = Field.Abwd (Structfield)

  module TermFam = struct
    type ('mode, 'a, 's) t = ('mode, 'a, 's) Term.term
  end

  module ModalTermCube = Modality.Cube (TermFam)

  (* A typechecked De Bruijn index is a well-scoped natural number together with a definite strict face (the top face, if none was supplied explicitly).  Unlike a raw De Bruijn index, the scoping is by a tbwd rather than a type-level nat.  This allows the face to also be well-scoped: its codomain must be the dimension appearing in the hctx at that position.  And since we already have defined Tbwd.insert, we can re-use that instead of re-defining this inductively. *)
  type _ index = Index : ('a, 'n, 'b) Tbwd.insert * ('k, 'n) sface -> 'b index

  type (_, _, _) term =
    (* Most term-formers only appear in kinetic (ordinary) terms. *)
    | Var : 'a index -> ('mode, 'a, kinetic) term
    | Const : Constant.t -> ('mode, 'a, kinetic) term
    | Meta : ('mode, 'x, 'b, 'l) Meta.t * 's energy -> ('mode, 'b, 's) term
    (* Normally, checked metavariables don't require an environment attached, but they do when they arise by readback from a value metavariable. *)
    | MetaEnv : ('mode, 'x, 'b, 's) Meta.t * ('mode, 'a, 'n, 'b) env -> ('mode, 'a, kinetic) term
    | Field :
        ('mode, 'a, kinetic) term * 'i Field.t * ('n, 't, 'i) insertion
        -> ('mode, 'a, kinetic) term
    | UU : 'mode Mode.t * 'n D.t -> ('mode, 'a, kinetic) term
    | Inst :
        ('mode, 'a, kinetic) term * ('m, 'n, 'mn, ('mode, 'a, kinetic) term) TubeOf.t
        -> ('mode, 'a, kinetic) term
    | Pi :
        'n variables
        * ('dom, 'modality, 'mode) Modality.t
        * ('n, ('dom, 'a, kinetic) term) CubeOf.t
        * ('n, 'mode * 'a) CodCube.t
        -> ('mode, 'a, kinetic) term
    | App :
        ('mode, 'a, kinetic) term
        * ('dom, 'modality, 'mode) Modality.t
        * ('n, ('dom, 'a, kinetic) term) CubeOf.t
        -> ('mode, 'a, kinetic) term
    | Constr :
        Constr.t * 'n D.t * ('n, 'mode, 'a, kinetic) ModalTermCube.t list
        -> ('mode, 'a, kinetic) term
    | Act :
        ('mode, 'a, kinetic) term
        * ('m, 'n) deg
        * ([ `Type | `Function | `Other ] * [ `Canonical | `Other ])
        -> ('mode, 'a, kinetic) term
    | Key :
        ('mode, 'a, kinetic) term * ('a, 'c, 'ac) Tbwd.append * ('mode, 'mu, 'nu, 'cod) Modalcell.t
        -> ('mode, 'ac, kinetic) term
    (* The term being bound in a 'let' is always kinetic.  Thus, if the supplied bound term is potential, the "bound term" here must be the metavariable whose value is set to that term rather than to the (potential) term itself.  We don't need a term-level "letrec" since recursion is implemented in the typechecker by creating a new global metavariable. *)
    | Let :
        string option
        * ('dom, 'modality, 'mode) Modality.t
        * ('dom, 'a, kinetic) term
        * ('mode, ('a, D.zero) snoc, 's) term
        -> ('mode, 'a, 's) term
    (* Abstractions and structs can appear in any kind of term.  The dimension 'n is the substitution dimension of the type being checked against (function-type or codata/record).  *)
    | Lam : 'n variables * ('mode, ('a, 'n) snoc, 's) Term.term -> ('mode, 'a, 's) term
    | Struct : ('mode, 'n, 'a, 's, 'et) struct_args -> ('mode, 'a, 's) term
    (* Matches can only appear in non-kinetic terms.  The dimension 'n is the substitution dimension of the type of the variable being matched against. *)
    | Match : {
        tm : ('mode, 'a, kinetic) term;
        dim : 'n D.t;
        branches : ('mode, 'a, 'n) branch Constr.Map.t;
      }
        -> ('mode, 'a, potential) term
    (* A potential term is "realized" by kinetic terms, or canonical types, at its leaves. *)
    | Realize : ('mode, 'a, kinetic) term -> ('mode, 'a, potential) term
    | Canonical : ('mode, 'a) canonical -> ('mode, 'a, potential) term
    (* These operations are easy to evaluate because they are dual to corresponding operations on environments.  They never appear in the output of typechecking, but they are useful when constructing terms "by hand" in OCaml code, such as in fibrancy witnesses. *)
    | Unshift : 'n D.t * ('n, 'b, 'nb) Plusmap.t * ('mode, 'nb, 's) term -> ('mode, 'b, 's) term
    | Unact : ('m, 'n) op * ('mode, 'b, 's) term -> ('mode, 'b, 's) term
    | Shift : 'n D.t * ('n, 'b, 'nb) Plusmap.t * ('mode, 'b, 's) term -> ('mode, 'nb, 's) term
    | Weaken : ('mode, 'b, 's) term -> ('mode, ('b, 'n) snoc, 's) term

  and ('mode, 'n, 'a, 's, 'et) struct_args = {
    dim : 'n D.t;
    fields : ('mode * ('n * 'a * 's * 'et)) StructfieldAbwd.t;
    eta : ('s, 'et) eta;
    energy : 's energy;
  }

  (* A branch of a match binds a number of new variables.  If it is a higher-dimensional match, then each of those "variables" is actually a full cube of variables.  In addition, its context must be permuted to put those new variables before the existing variables that are now defined in terms of them. *)
  and (_, _, _) branch =
    | Branch :
        ('a, 'b, 'n, 'ab) Tbwd.snocs * ('c, 'ab) Tbwd.permute * ('mode, 'c, potential) term
        -> ('mode, 'a, 'n) branch
    (* A branch that was refuted during typechecking doesn't need a body to compute with, but we still mark its presence as a signal that it should be stuck (this can occur when normalizing in an inconsistent context). *)
    | Refute

  (* A canonical type is either a datatype or a codatatype/record. *)
  and (_, _) canonical =
    (* A datatype stores its family of constructors, whether it is discrete, and also its number of indices.  (The former is not determined in the latter if there happen to be zero constructors). *)
    | Data : {
        indices : 'i Fwn.t;
        constrs : (Constr.t, ('mode, 'a, 'i) dataconstr) Abwd.t;
        discrete : [ `Yes | `Maybe | `No ];
      }
        -> ('mode, 'a) canonical
    | Codata : ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et) codata_args -> ('mode, 'a) canonical

  and ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et) codata_args = {
    (* An eta flag and its opacity *)
    eta : (potential, 'et) eta;
    opacity : opacity;
    (* An intrinsic dimension (like Gel) *)
    dim : 'n D.t;
    (* The termctx in which it was checked, since that is needed to eval-readback the env to degenerate it when checking higher fields. *)
    termctx : ('mode, 'c, ('a, 'n) snoc) termctx option;
    (* A family of fields, each with a type that depends on one additional variable belonging to the codatatype itself (usually by way of its previous fields).  We retain the order of the fields by storing them in an Abwd rather than a Map so as to enable positional access as well as named access. *)
    fields : ('mode * 'a * 'n * 'et) CodatafieldAbwd.t;
    (* We partially compute the fibrancy fields at typechecking time, although we don't finish the computation until we need it.  Since the fibrancy fields include those of all the higher identity types, if we did all the computation eagerly it would be infinite, and if we made it Lazy in the naive way then it wouldn't be marshalable.  *)
    fibrancy : ('mode, 'n, 'n, 'nh, 'a, 'ha, 'et) codata_fibrancy;
    (* Fibrancy of glue-types is computed separately and stored, so we remember whether this is a glue-type. *)
    is_glue : ('n, 'a, 'et) is_glue option;
  }

  and ('mode, 'g, 'n, 'nh, 'b, 'hb, 'et) codata_fibrancy = {
    (* The original intrinsic gel/glue dimension *)
    glue : 'g D.t;
    (* The overall dimension.  Note that when it appears as a field of codata_args, above, these two dimensions are the same.  However, as we apply the corecursive 'id' field in computing fibrancy of higher versions of a codatatype, the overall dimension n increases but the glue dimension g does not. *)
    dim : 'n D.t;
    length : 'b Plusmap.OfDom.t;
    plusmap : (Hott.dim, 'b, 'hb) Plusmap.t;
    eta : (potential, 'et) eta;
    (* The codatatype itself. *)
    ty : ('mode, 'b, kinetic) term;
    dimh : ('n, Hott.dim, 'nh) D.plus;
    (* The fields of the struct that is the output of the transport and lifting operations. *)
    trr : ('mode * ('n * ('hb, D.zero) snoc * potential * 'et)) StructfieldAbwd.t;
    trl : ('mode * ('n * ('hb, D.zero) snoc * potential * 'et)) StructfieldAbwd.t;
    (* These are one-higher-dimensional because the result of lifting lies in a degenerated version of the codatatype. *)
    liftr : ('mode * ('nh * ('hb, D.zero) snoc * potential * 'et)) StructfieldAbwd.t;
    liftl : ('mode * ('nh * ('hb, D.zero) snoc * potential * 'et)) StructfieldAbwd.t;
  }

  (* A datatype constructor has a telescope of arguments and a list of index values depending on those arguments. *)
  and (_, _, _) dataconstr =
    | Dataconstr : {
        args : ('mode, 'p, 'a, 'pa) tel;
        indices : (('mode, 'pa, kinetic) term, 'i) Vec.t;
      }
        -> ('mode, 'p, 'i) dataconstr

  (* A telescope is a list of types, each dependent on the previous ones.  Note that 'a and 'ab are lists of dimensions, but 'b is just a forwards natural number counting the number of *zero-dimensional* variables added to 'a to get 'ab.  *)
  and ('mode, 'a, 'b, 'ab) tel =
    | Emp : ('mode, 'a, Fwn.zero, 'a) tel
    | Ext :
        string option
        * ('dom, 'modality, 'mode) Modality.t
        * ('dom, 'a, kinetic) term
        * ('mode, ('a, D.zero) snoc, 'b, 'ab) tel
        -> ('mode, 'a, 'b Fwn.suc, 'ab) tel

  (* A version of an environment that involves terms rather than values.  Used mainly when reading back metavariables.  The first argument is the mode, the second is the checked-length of the context *in* which the environment is defined (its domain, as a context morphism), the third is its dimension, and the fourth is the checked-length of the context of types of the values in the environment (its codomain, as a context morphism).  *)
  and (_, _, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'a, 'n, emp) env
    | Ext :
        ('mode, 'a, 'n, 'b) env
        * ('n, 'k, 'nk) D.plus
        * ('dom, 'modality, 'mode) Modality.t
        * ('nk, ('dom, 'a, kinetic) term) CubeOf.t
        -> ('mode, 'a, 'n, ('b, 'k) snoc) env
    (* There is a decision to be made here about how to deal with keys in a term environment.  The problem is that the part of the environment to the left of a key must be defined in a context that has the locks corresponding to the codomain of that keys removed, along with everything to their right.  But simply removing variables from the context fubars the De Bruijn indices.  We could replace the removed indices in the context by a placeholder that extends out its length while containing no data.  Instead, we choose to allow the domain length of a term environment to increase when we pass a key.  This means when working with such environments we must shrink the domain context when we pass a key.  To be really pedantic we should insist that 'c is a Tlist of dimensions, but we don't currently bother. *)
    | Key :
        ('mode, 'a, 'n, 'b) env * ('a, 'c, 'ac) Tbwd.append * ('dom, 'mu, 'nu, 'mode) Modalcell.t
        -> ('dom, 'ac, 'n, 'b) env

  (* A termctx is a data structure analogous to a Ctx.t, but using terms rather than values (and thus we will not explain its structure here; see ctx.ml).  This is used to store the context of a metavariable, as the value context containing level variables is too volatile to store there.  We also store it (lazily) with a codatatype that has higher fields, so we can use it to read back the closure environment to degenerate it. *)
  and ('mode, 'b) binding = {
    ty : ('mode, 'b, kinetic) term;
    tm : ('mode, 'b, kinetic) term option;
  }

  and (_, _) has_fields =
    | No_fields : ('m, N.zero) has_fields
    | Has_fields : (D.zero, 'f2) has_fields

  and (_, _, _, _, _, _) entry =
    | Vis : {
        dim : 'm D.t;
        modality : ('dom, 'modality, 'mode) Modality.t;
        plusdim : ('m, 'n, 'mn) D.plus;
        vars : (N.zero, 'n, string option, 'f1) NICubeOf.t;
        (* The reason for the "snoc" here is so that some of the terms and types in these bindings can refer to other ones.  Of course it should really be only the *later* ones that can refer to the *earlier* ones, but we don't have a way to specify that in the type parameters. *)
        bindings : ('mn, ('dom, ('b, 'mn) snoc) binding) CubeOf.t;
        hasfields : ('m, 'f2) has_fields;
        fields : (D.zero Field.t * string * ('dom, ('b, 'mn) snoc, kinetic) term, 'f2) Bwv.t;
        fplus : ('f1, 'f2, 'f) N.plus;
      }
        -> ('dom, 'modality, 'mode, 'b, 'f, 'mn) entry
    | Invis :
        ('dom, 'modality, 'mode) Modality.t * ('n, ('dom, ('b, 'n) snoc) binding) CubeOf.t
        -> ('dom, 'modality, 'mode, 'b, N.zero, 'n) entry

  and (_, _, _) ordered_termctx =
    | Emp : 'mode Mode.t -> ('mode, N.zero, emp) ordered_termctx
    | Ext :
        ('mode, 'a, 'b) ordered_termctx
        * ('dom, 'modality, 'mode, 'b, 'x, 'n) entry
        * ('a, 'x, 'ax) N.plus
        -> ('mode, 'ax, ('b, 'n) snoc) ordered_termctx
    | Lock :
        ('mode, 'a, 'b) ordered_termctx * ('dom, 'modality, 'mode) Modality.t * bool
        -> ('dom, 'a, 'b) ordered_termctx

  and ('mode, 'a, 'b) termctx =
    | Permute : ('a, 'i) N.perm * ('mode, 'i, 'b) ordered_termctx -> ('mode, 'a, 'b) termctx
end

include Term

(* Find the name of the (n+1)st abstracted variable, where n is the length of a supplied argument list.  Doesn't "look through" branches or cobranches or into leaves. *)
let rec nth_var : type mode a b s. (mode, a, s) term -> b Bwd.t -> any_variables option =
 fun tr args ->
  match tr with
  | Lam (x, body) -> (
      match args with
      | Emp -> Some (Any x)
      | Snoc (args, _) -> nth_var body args)
  | _ -> None

let pi x modality dom cod = Pi (x, modality, CubeOf.singleton dom, CodCube.singleton (Cod cod))
let app fn modality arg = App (fn, modality, CubeOf.singleton arg)
let apps fn modality args = List.fold_left (fun f -> app f modality) fn args

(* let constr name args = Constr (name, D.zero, List.map CubeOf.singleton args) *)
let field tm f = Field (tm, f, ins_zero D.zero)

module Telescope = struct
  type ('mode, 'a, 'b, 'ab) t = ('mode, 'a, 'b, 'ab) Term.tel

  let rec length : type mode a b ab. (mode, a, b, ab) t -> b Fwn.t = function
    | Emp -> Zero
    | Ext (_, _, _, tel) -> Suc (length tel)

  let rec pis : type mode a b ab.
      (mode, a, b, ab) t -> (mode, ab, kinetic) term -> (mode, a, kinetic) term =
   fun doms cod ->
    match doms with
    | Emp -> cod
    | Ext (x, modality, dom, doms) -> pi (singleton_variables D.zero x) modality dom (pis doms cod)

  let rec lams : type mode a b ab.
      (mode, a, b, ab) t -> (mode, ab, kinetic) term -> (mode, a, kinetic) term =
   fun doms body ->
    match doms with
    | Emp -> body
    | Ext (x, _, _, doms) -> Lam (singleton_variables D.zero x, lams doms body)

  let rec snocs : type mode a b ab. (mode, a, b, ab) t -> (a, b, D.zero, ab) Tbwd.snocs = function
    | Emp -> Zero
    | Ext (_, _, _, tel) -> Suc (snocs tel)
end

let rec dim_term_env : type mode a n b. (mode, a, n, b) env -> n D.t = function
  | Emp (_, n) -> n
  | Ext (e, _, _, _) -> dim_term_env e
  | Key (e, _, _) -> dim_term_env e

let dim_entry : type dom modality mode b f n. (dom, modality, mode, b, f, n) entry -> n D.t =
  function
  | Vis { bindings; _ } | Invis (_, bindings) -> CubeOf.dim bindings

module Termctx = struct
  type ('mode, 'a, 'b) ordered = ('mode, 'a, 'b) ordered_termctx
  type ('mode, 'a, 'b) t = ('mode, 'a, 'b) termctx

  let rec ordered_dbwd : type mode a b. (mode, a, b) ordered_termctx -> b Dbwd.t = function
    | Emp _ -> Word Zero
    | Ext (ctx, e, _) ->
        let (Word b) = ordered_dbwd ctx in
        Word (Suc (b, dim_entry e))
    | Lock (ctx, _, _) -> ordered_dbwd ctx

  let dbwd (Permute (_, ctx)) = ordered_dbwd ctx

  let ordered_ext_let : type dom modality mode a b.
      (mode, a, b) ordered_termctx ->
      string option ->
      (dom, modality, mode) Modality.t ->
      (dom, (b, D.zero) snoc) binding ->
      (mode, a N.suc, (b, D.zero) snoc) ordered_termctx =
   fun ctx x modality b ->
    Ext
      ( ctx,
        Vis
          {
            dim = D.zero;
            modality;
            plusdim = D.plus_zero D.zero;
            vars = NICubeOf.singleton x;
            bindings = CubeOf.singleton b;
            hasfields = No_fields;
            fields = Emp;
            fplus = Zero;
          },
        Suc Zero )

  let ext_let (Permute (p, ctx)) modality xs b =
    let ctx = ordered_ext_let ctx modality xs b in
    Permute (Insert (p, Top), ctx)

  let ext (Permute (p, ctx)) modality xs ty =
    let ctx = ordered_ext_let ctx modality xs { ty; tm = None } in
    Permute (Insert (p, Top), ctx)

  let rec ordered_mode : type mode a b. (mode, a, b) ordered_termctx -> mode Mode.t = function
    | Emp mode -> mode
    | Ext (ctx, _, _) -> ordered_mode ctx
    | Lock (_, lock, _) -> Modality.dom lock

  let mode (Permute (_, ctx)) = ordered_mode ctx
end
