open Bwd
open Util
open Modal
open Tbwd
open Dim
open Tctx
include Variables
include Energy

type (_, _, _, _) is_glue =
  | Glue :
      ( 'mode,
        Hott.dim,
        ( ( (('mode emp, ('mode id, D.zero) dim_entry) snoc, ('mode id, D.zero) dim_entry) snoc,
            ('mode id, D.zero) dim_entry )
          snoc,
          ('mode id, D.zero) dim_entry )
        snoc,
        has_eta )
      is_glue

(* ******************** Typechecked terms ******************** *)

(* Typechecked, but unevaluated, terms.  Uses De Bruijn indices that are intrinsically well-scoped by Tctxs, but are no longer separated into synthesizing and checking; hence without type ascriptions.  Note that extending a Tctx by a dimension 'k means adding a whole cube of new variables, which are indexed by the position of that dimension together with a strict face of it.  (At user-level, those variables may all be accessed as faces of one "cube variable", or they may have independent names, but internally there is no difference.)

   Incorporates information appropriate to the internal syntax that is constructed during typechecking, e.g. applications and abstractions are grouped by a dimension, since this can be inferred during typechecking, from the synthesized type of a function being applied and from the pi-type the lambda is being checked against, respectively.  Similarly, we have instantiations of higher-dimensional types obtained by applying them to a tube of boundary terms. *)

(* The codomain of a higher-dimensional pi-type is a cube of terms with bound variables whose number varies with the face of the cube.  We can enforce this with a parametrized instance of Cube, but it has to be defined recursively with term using a recursive module (like BindCube in Value; see there for more commentary).  Since term has three type parameters ('mode, 'a, 's) but Cube requires a Fam2 with two parameters, we pack 'mode * 'a into the second parameter of CodFam using a GADT constructor. *)
module rec Term : sig
  module CodFam : sig
    type (_, _) t =
      | Cod :
          ('mode, ('a, ('modality, 'k) dim_entry) snoc, kinetic) Term.term
          -> ('k, 'mode * 'modality * 'a) t
  end

  module CodCube : module type of Cube (CodFam)

  module PlusFam : sig
    type (_, _) some =
      | PlusFam :
          (('r, 'b, 'rb, 'mode) plusmap * ('mode, 'rb, potential) Term.term)
          -> ('r, 'mode * 'b) some

    type ('r, 'mb) t = ('r, 'mb) some option
  end

  module PlusPbijmap : module type of Pbijmap (PlusFam)

  module Codatafield : sig
    type (_, _) t =
      | Lower :
          ('mode, ('a, ('mode id, 'n) dim_entry) snoc, kinetic) Term.term
          -> (D.zero, 'mode * 'a * 'n * 'et) t
      | Higher :
          ('i, ('a, ('mode id, D.zero) dim_entry) snoc, 'ian, 'mode) plusmap
          * ('mode, 'ian, kinetic) Term.term
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

  type (_, _, _, _) modal_term =
    | Modal :
        ('dom, 'modality, 'mode) Modality.t
        * ('a, 'mode, 'modality, 'dom, 'am) plus_lock
        * ('dom, 'am, 's) Term.term
        -> ('mode, 'modality, 'a, 's) modal_term

  type (_, _, _, _, _, _) modal_term_cube =
    | Modal :
        ('dom, 'modality, 'mode) Modality.t
        * ('a, 'mode, 'modality, 'dom, 'am) plus_lock
        * ('n, ('dom, 'am, 's) Term.term) CubeOf.t
        -> ('n, 'dom, 'modality, 'mode, 'a, 's) modal_term_cube

  type (_, _, _, _) any_modal_term_cube =
    | Modal :
        ('dom, 'modality, 'mode) Modality.t
        * ('a, 'mode, 'modality, 'dom, 'am) plus_lock
        * ('n, ('dom, 'am, 's) Term.term) CubeOf.t
        -> ('n, 'mode, 'a, 's) any_modal_term_cube

  type (_, _, _) term =
    | Var : ('mode, 'a) index -> ('mode, 'a, kinetic) term
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
        * ('n, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube
        * ('n, 'mode * 'modality * 'a) CodCube.t
        -> ('mode, 'a, kinetic) term
    | App :
        ('mode, 'a, kinetic) term * ('n, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube
        -> ('mode, 'a, kinetic) term
    | Constr :
        Constr.t * 'n D.t * ('n, 'mode, 'a, kinetic) any_modal_term_cube list
        -> ('mode, 'a, kinetic) term
    | Act :
        ('mode, 'a, kinetic) term
        * ('m, 'n) deg
        * ([ `Type | `Function | `Other ] * [ `Canonical | `Other ])
        -> ('mode, 'a, kinetic) term
    | Key : {
        tm : ('mode, 'am, kinetic) term;
        cell : ('mode, 'mu, 'nu, 'cod) Modalcell.t;
        plus_tgt : ('a, 'cod, 'nu, 'mode, 'ac) plus_with_locks;
        plus_src : ('a, 'cod, 'mu, 'mode, 'am) plus_lock;
      }
        -> ('mode, 'ac, kinetic) term
    | Let :
        string option
        * ('mode, 'modality, 'a, kinetic) modal_term
        * ('mode, ('a, ('modality, D.zero) dim_entry) snoc, 's) term
        -> ('mode, 'a, 's) term
    | Lam :
        'n variables
        * ('dom, 'modality, 'mode) Modality.t
        * ('mode, ('a, ('modality, 'n) dim_entry) snoc, 's) Term.term
        -> ('mode, 'a, 's) term
    | Struct : ('mode, 'n, 'a, 's, 'et) struct_args -> ('mode, 'a, 's) term
    | Match : {
        tm : ('mode, 'a, kinetic) term;
        dim : 'n D.t;
        branches : ('mode, 'a, 'n) branch Constr.Map.t;
      }
        -> ('mode, 'a, potential) term
    | Realize : ('mode, 'a, kinetic) term -> ('mode, 'a, potential) term
    | Canonical : ('mode, 'a) canonical -> ('mode, 'a, potential) term
    | Unshift :
        'n D.t * ('n, 'b, 'nb, 'mode) plusmap * ('mode, 'nb, 's) term
        -> ('mode, 'b, 's) term
    | Unact : ('m, 'n) op * ('mode, 'b, 's) term -> ('mode, 'b, 's) term
    | Shift : 'n D.t * ('n, 'b, 'nb, 'mode) plusmap * ('mode, 'b, 's) term -> ('mode, 'nb, 's) term
    | Weaken : ('mode, 'b, 's) term -> ('mode, ('b, ('modality, 'n) dim_entry) snoc, 's) term

  and ('mode, 'n, 'a, 's, 'et) struct_args = {
    dim : 'n D.t;
    fields : ('mode * ('n * 'a * 's * 'et)) StructfieldAbwd.t;
    eta : ('s, 'et) eta;
    energy : 's energy;
  }

  and (_, _, _) branch =
    | Branch : {
        annotate : ('n, 'mode, 'annotations, 'mode, 'mode, 'b, 'mode) VarAnnotate.fwd_t;
        comp : ('mode, 'b, 'mode, 'a, unit, 'ab) Tctx.bcomp;
        perm : ('c, 'ab) permute;
        tm : ('mode, 'c, potential) term;
      }
        -> ('mode, 'a, 'n) branch
    | Refute

  and (_, _) canonical =
    | Data : {
        indices : 'i Fwn.t;
        constrs : (Constr.t, ('mode, 'a, 'i) dataconstr) Abwd.t;
        discrete : [ `Yes | `Maybe | `No ];
        (* Variable-name hints, for displaying anonymous variables of this type. *)
        hints : hints;
      }
        -> ('mode, 'a) canonical
    | Codata : ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et) codata_args -> ('mode, 'a) canonical

  and ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    (* Variable-name hints, for displaying anonymous variables of this type. *)
    hints : hints;
    dim : 'n D.t;
    termctx : ('mode, 'c, ('a, ('mode id, 'n) dim_entry) snoc) termctx option;
    fields : ('mode * 'a * 'n * 'et) CodatafieldAbwd.t;
    fibrancy : ('mode, 'n, 'n, 'nh, 'a, 'ha, 'et) codata_fibrancy;
    is_glue : ('mode, 'n, 'a, 'et) is_glue option;
  }

  and ('mode, 'g, 'n, 'nh, 'b, 'hb, 'et) codata_fibrancy = {
    glue : 'g D.t;
    dim : 'n D.t;
    length : ('mode, 'b) Tctx.t;
    plusmap : (Hott.dim, 'b, 'hb, 'mode) plusmap;
    eta : (potential, 'et) eta;
    ty : ('mode, 'b, kinetic) term;
    dimh : ('n, Hott.dim, 'nh) D.plus;
    trr :
      ('mode * ('n * ('hb, ('mode id, D.zero) dim_entry) snoc * potential * 'et)) StructfieldAbwd.t;
    trl :
      ('mode * ('n * ('hb, ('mode id, D.zero) dim_entry) snoc * potential * 'et)) StructfieldAbwd.t;
    liftr :
      ('mode * ('nh * ('hb, ('mode id, D.zero) dim_entry) snoc * potential * 'et)) StructfieldAbwd.t;
    liftl :
      ('mode * ('nh * ('hb, ('mode id, D.zero) dim_entry) snoc * potential * 'et)) StructfieldAbwd.t;
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
        * ('mode, 'modality, 'a, kinetic) modal_term
        * ('mode, ('a, ('modality, D.zero) dim_entry) snoc, 'b, 'ab) tel
        -> ('mode, 'a, 'b Fwn.suc, 'ab) tel

  and (_, _, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'a, 'n, 'mode emp) env
    | Ext :
        ('mode, 'a, 'n, 'b) env
        * ('n, 'k, 'nk) D.plus
        * ('nk, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube
        -> ('mode, 'a, 'n, ('b, ('modality, 'k) dim_entry) snoc) env
    | Key : {
        env : ('cod, 'a, 'n, 'b) env;
        cell : ('mode, 'mu, 'nu, 'cod) Modalcell.t;
        plus_tgt : ('a, 'cod, 'nu, 'mode, 'ac) plus_with_locks;
        plus_src : ('b, 'cod, 'mu, 'mode, 'bmu) plus_lock;
      }
        -> ('mode, 'ac, 'n, 'bmu) env

  and ('mode, 'b) binding = {
    ty : ('mode, 'b, kinetic) term;
    tm : ('mode, 'b, kinetic) term option;
  }

  and (_, _) has_fields =
    | No_fields : ('m, N.zero) has_fields
    | Has_fields : (D.zero, 'f2) has_fields

  and (_, _, _, _, _, _, _) entry =
    | Vis : {
        dim : 'm D.t;
        plus_lock : (('b, ('modality, 'mn) dim_entry) snoc, 'mode, 'modality, 'dom, 'bm) plus_lock;
        plusdim : ('m, 'n, 'mn) D.plus;
        vars : (N.zero, 'n, binder_name, 'f1) NICubeOf.t;
        bindings : ('mn, ('dom, 'bm) binding) CubeOf.t;
        hasfields : ('m, 'f2) has_fields;
        fields : (D.zero Field.t * string * ('dom, 'bm, kinetic) term, 'f2) Bwv.t;
        fplus : ('f1, 'f2, 'f) N.plus;
      }
        -> ('dom, 'modality, 'mode, 'b, 'bm, 'f, 'mn) entry
    | Invis :
        (('b, ('modality, 'n) dim_entry) snoc, 'mode, 'modality, 'dom, 'bm) plus_lock
        * ('n, ('dom, 'bm) binding) CubeOf.t
        * hints
        -> ('dom, 'modality, 'mode, 'b, 'bm, N.zero, 'n) entry

  and (_, _, _) ordered_termctx =
    | Emp : 'mode Mode.t -> ('mode, N.zero, (unit id, 'mode proj) suc) ordered_termctx
    | Ext :
        ('mode, 'a, 'b) ordered_termctx
        * ('dom, 'modality, 'mode, 'b, 'bm, 'x, 'n) entry
        * ('a, 'x, 'ax) N.plus
        -> ('mode, 'ax, ('b, ('modality, 'n) dim_entry) snoc) ordered_termctx
    | Lock :
        ('cod, 'a, 'b) ordered_termctx * ('dom, 'modality, 'cod) Modality.gen
        -> ('dom, 'a, ('b, 'modality lock_entry) snoc) ordered_termctx
    | Parametric_lock : ('mode, 'a, 'b) ordered_termctx -> ('mode, 'a, 'b) ordered_termctx

  and ('mode, 'a, 'b) termctx =
    | Permute : ('a, 'i) N.permute * ('mode, 'i, 'b) ordered_termctx -> ('mode, 'a, 'b) termctx
end = struct
  module CodFam = struct
    type ('k, _) t =
      | Cod :
          ('mode, ('a, ('modality, 'k) dim_entry) snoc, kinetic) Term.term
          -> ('k, 'mode * 'modality * 'a) t
  end

  module CodCube = Cube (CodFam)

  module PlusFam = struct
    type (_, _) some =
      | PlusFam :
          (('r, 'b, 'rb, 'mode) plusmap * ('mode, 'rb, potential) Term.term)
          -> ('r, 'mode * 'b) some

    type ('r, 'mb) t = ('r, 'mb) some option
  end

  module PlusPbijmap = Pbijmap (PlusFam)

  module Codatafield = struct
    (* MODALTODO: Allow modal fields *)
    type (_, _) t =
      | Lower :
          ('mode, ('a, ('mode id, 'n) dim_entry) snoc, kinetic) Term.term
          -> (D.zero, 'mode * 'a * 'n * 'et) t
      | Higher :
          ('i, ('a, ('mode id, D.zero) dim_entry) snoc, 'ian, 'mode) plusmap
          * ('mode, 'ian, kinetic) Term.term
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

  (* A modal term is a term in a context extended by a lock on a given modality. *)
  type (_, _, _, _) modal_term =
    | Modal :
        ('dom, 'modality, 'mode) Modality.t
        * ('a, 'mode, 'modality, 'dom, 'am) plus_lock
        * ('dom, 'am, 's) Term.term
        -> ('mode, 'modality, 'a, 's) modal_term

  (* A modal term cube is a cube of terms in a context extended by a lock by a given modality. *)
  type (_, _, _, _, _, _) modal_term_cube =
    | Modal :
        ('dom, 'modality, 'mode) Modality.t
        * ('a, 'mode, 'modality, 'dom, 'am) plus_lock
        * ('n, ('dom, 'am, 's) Term.term) CubeOf.t
        -> ('n, 'dom, 'modality, 'mode, 'a, 's) modal_term_cube

  (* Similarly, but when we don't know what the modality might be. *)
  type (_, _, _, _) any_modal_term_cube =
    | Modal :
        ('dom, 'modality, 'mode) Modality.t
        * ('a, 'mode, 'modality, 'dom, 'am) plus_lock
        * ('n, ('dom, 'am, 's) Term.term) CubeOf.t
        -> ('n, 'mode, 'a, 's) any_modal_term_cube

  type (_, _, _) term =
    (* Most term-formers only appear in kinetic (ordinary) terms. *)
    | Var : ('mode, 'a) index -> ('mode, 'a, kinetic) term
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
        * ('n, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube
        * ('n, 'mode * 'modality * 'a) CodCube.t
        -> ('mode, 'a, kinetic) term
    | App :
        ('mode, 'a, kinetic) term * ('n, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube
        -> ('mode, 'a, kinetic) term
    | Constr :
        Constr.t * 'n D.t * ('n, 'mode, 'a, kinetic) any_modal_term_cube list
        -> ('mode, 'a, kinetic) term
    | Act :
        ('mode, 'a, kinetic) term
        * ('m, 'n) deg
        * ([ `Type | `Function | `Other ] * [ `Canonical | `Other ])
        -> ('mode, 'a, kinetic) term
    (* A keyed term strips off part of the context that contains locks adding up to the codomain of the key cell, then replaces them by the domain of that cell for the body term. *)
    | Key : {
        tm : ('mode, 'am, kinetic) term;
        cell : ('mode, 'mu, 'nu, 'cod) Modalcell.t;
        plus_tgt : ('a, 'cod, 'nu, 'mode, 'ac) plus_with_locks;
        plus_src : ('a, 'cod, 'mu, 'mode, 'am) plus_lock;
      }
        -> ('mode, 'ac, kinetic) term
    (* The term being bound in a 'let' is always kinetic.  Thus, if the supplied bound term is potential, the "bound term" here must be the metavariable whose value is set to that term rather than to the (potential) term itself.  We don't need a term-level "letrec" since recursion is implemented in the typechecker by creating a new global metavariable. *)
    | Let :
        string option
        * ('mode, 'modality, 'a, kinetic) modal_term
        (* A let is also always zero-dimensional. *)
        * ('mode, ('a, ('modality, D.zero) dim_entry) snoc, 's) term
        -> ('mode, 'a, 's) term
    (* Abstractions and structs can appear in any kind of term.  The dimension 'n is the substitution dimension of the type being checked against (function-type or codata/record).  *)
    | Lam :
        'n variables
        * ('dom, 'modality, 'mode) Modality.t
        * ('mode, ('a, ('modality, 'n) dim_entry) snoc, 's) Term.term
        -> ('mode, 'a, 's) term
    | Struct : ('mode, 'n, 'a, 's, 'et) struct_args -> ('mode, 'a, 's) term
    (* Matches can only appear in potential terms.  The dimension 'n is the substitution dimension of the type of the variable being matched against. *)
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
    | Unshift :
        'n D.t * ('n, 'b, 'nb, 'mode) plusmap * ('mode, 'nb, 's) term
        -> ('mode, 'b, 's) term
    | Unact : ('m, 'n) op * ('mode, 'b, 's) term -> ('mode, 'b, 's) term
    | Shift : 'n D.t * ('n, 'b, 'nb, 'mode) plusmap * ('mode, 'b, 's) term -> ('mode, 'nb, 's) term
    | Weaken : ('mode, 'b, 's) term -> ('mode, ('b, ('modality, 'n) dim_entry) snoc, 's) term

  and ('mode, 'n, 'a, 's, 'et) struct_args = {
    dim : 'n D.t;
    fields : ('mode * ('n * 'a * 's * 'et)) StructfieldAbwd.t;
    eta : ('s, 'et) eta;
    energy : 's energy;
  }

  (* A branch of a match binds a number of new variables.  If it is a higher-dimensional match, then each of those "variables" is actually a full cube of variables.  In addition, its context must be permuted to put those new variables before the existing variables that are now defined in terms of them.  Finally, each of the variables might be annotated by a different modality, so we include a list of such modalities and make it into a tctx extension that all have the same dimension. *)
  and (_, _, _) branch =
    | Branch : {
        annotate : ('n, 'mode, 'annotations, 'mode, 'mode, 'b, 'mode) VarAnnotate.fwd_t;
        comp : ('mode, 'b, 'mode, 'a, unit, 'ab) Tctx.bcomp;
        perm : ('c, 'ab) permute;
        tm : ('mode, 'c, potential) term;
      }
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
        (* Variable-name hints, for displaying anonymous variables of this type. *)
        hints : hints;
      }
        -> ('mode, 'a) canonical
    | Codata : ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et) codata_args -> ('mode, 'a) canonical

  and ('mode, 'n, 'c, 'a, 'nh, 'ha, 'et) codata_args = {
    (* An eta flag and its opacity *)
    eta : (potential, 'et) eta;
    opacity : opacity;
    (* Variable-name hints, for displaying anonymous variables of this type. *)
    hints : hints;
    (* An intrinsic dimension (like Gel) *)
    dim : 'n D.t;
    (* The termctx in which it was checked, since that is needed to eval-readback the env to degenerate it when checking higher fields. *)
    termctx : ('mode, 'c, ('a, ('mode id, 'n) dim_entry) snoc) termctx option;
    (* A family of fields, each with a type that depends on one additional variable belonging to the codatatype itself (usually by way of its previous fields).  We retain the order of the fields by storing them in an Abwd rather than a Map so as to enable positional access as well as named access. *)
    fields : ('mode * 'a * 'n * 'et) CodatafieldAbwd.t;
    (* We partially compute the fibrancy fields at typechecking time, although we don't finish the computation until we need it.  Since the fibrancy fields include those of all the higher identity types, if we did all the computation eagerly it would be infinite, and if we made it Lazy in the naive way then it wouldn't be marshalable.  *)
    fibrancy : ('mode, 'n, 'n, 'nh, 'a, 'ha, 'et) codata_fibrancy;
    (* Fibrancy of glue-types is computed separately and stored, so we remember whether this is a glue-type. *)
    is_glue : ('mode, 'n, 'a, 'et) is_glue option;
  }

  and ('mode, 'g, 'n, 'nh, 'b, 'hb, 'et) codata_fibrancy = {
    (* The original intrinsic gel/glue dimension *)
    glue : 'g D.t;
    (* The overall dimension.  Note that when it appears as a field of codata_args, above, these two dimensions are the same.  However, as we apply the corecursive 'id' field in computing fibrancy of higher versions of a codatatype, the overall dimension n increases but the glue dimension g does not. *)
    dim : 'n D.t;
    length : ('mode, 'b) Tctx.t;
    plusmap : (Hott.dim, 'b, 'hb, 'mode) plusmap;
    eta : (potential, 'et) eta;
    (* The codatatype itself. *)
    ty : ('mode, 'b, kinetic) term;
    dimh : ('n, Hott.dim, 'nh) D.plus;
    (* The fields of the struct that is the output of the transport and lifting operations. *)
    trr :
      ('mode * ('n * ('hb, ('mode id, D.zero) dim_entry) snoc * potential * 'et)) StructfieldAbwd.t;
    trl :
      ('mode * ('n * ('hb, ('mode id, D.zero) dim_entry) snoc * potential * 'et)) StructfieldAbwd.t;
    (* These are one-higher-dimensional because the result of lifting lies in a degenerated version of the codatatype. *)
    liftr :
      ('mode * ('nh * ('hb, ('mode id, D.zero) dim_entry) snoc * potential * 'et)) StructfieldAbwd.t;
    liftl :
      ('mode * ('nh * ('hb, ('mode id, D.zero) dim_entry) snoc * potential * 'et)) StructfieldAbwd.t;
  }

  (* A datatype constructor has a telescope of arguments and a list of index values depending on those arguments. *)
  and (_, _, _) dataconstr =
    | Dataconstr : {
        args : ('mode, 'p, 'a, 'pa) tel;
        indices : (('mode, 'pa, kinetic) term, 'i) Vec.t;
      }
        -> ('mode, 'p, 'i) dataconstr

  (* A telescope is a list of types, each dependent on the previous ones.  Note that 'a and 'ab are lists of dimensions, but 'b is just a forwards natural number counting the number of *zero-dimensional* variables added to 'a to get 'ab.  The variables bound in a telescope are all zero-dimensional, but they can be nontrivially modally annotated.  *)
  and ('mode, 'a, 'b, 'ab) tel =
    | Emp : ('mode, 'a, Fwn.zero, 'a) tel
    | Ext :
        string option
        * ('mode, 'modality, 'a, kinetic) modal_term
        * ('mode, ('a, ('modality, D.zero) dim_entry) snoc, 'b, 'ab) tel
        -> ('mode, 'a, 'b Fwn.suc, 'ab) tel

  (* A version of an environment that involves terms rather than values.  Used mainly when reading back metavariables.  The first argument is the mode, the second is the checked-length of the context *in* which the environment is defined (its domain, as a context morphism), the third is its dimension, and the fourth is the checked-length of the context of types of the values in the environment (its codomain, as a context morphism).  *)
  and (_, _, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'a, 'n, 'mode emp) env
    | Ext :
        ('mode, 'a, 'n, 'b) env
        * ('n, 'k, 'nk) D.plus
        * ('nk, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube
        -> ('mode, 'a, 'n, ('b, ('modality, 'k) dim_entry) snoc) env
    (* There is a decision to be made here about how to deal with keys in a term environment.  The problem is that the part of the environment to the left of a key must be defined in a context that has the locks corresponding to the codomain of that key removed, along with everything interspersed with them and to their right.  But simply removing variables from the context fubars the De Bruijn indices.  We could replace the removed indices in the context by a placeholder that extends out its length while containing no data.  Instead, we choose to allow the domain length of a term environment to increase when we pass a key.  This means when working with such environments we must shrink the domain context when we pass a key. *)
    | Key : {
        env : ('cod, 'a, 'n, 'b) env;
        cell : ('mode, 'mu, 'nu, 'cod) Modalcell.t;
        plus_tgt : ('a, 'cod, 'nu, 'mode, 'ac) plus_with_locks;
        plus_src : ('b, 'cod, 'mu, 'mode, 'bmu) plus_lock;
      }
        -> ('mode, 'ac, 'n, 'bmu) env

  (* A termctx is a data structure analogous to a Ctx.t, but using terms rather than values (and thus we will not explain its structure here; see ctx.ml).  This is used to store the context of a metavariable, as the value context containing level variables is too volatile to store there.  We also store it (lazily) with a codatatype that has higher fields, so we can use it to read back the closure environment to degenerate it. *)
  and ('mode, 'b) binding = {
    ty : ('mode, 'b, kinetic) term;
    tm : ('mode, 'b, kinetic) term option;
  }

  and (_, _) has_fields =
    | No_fields : ('m, N.zero) has_fields
    | Has_fields : (D.zero, 'f2) has_fields

  and (_, _, _, _, _, _, _) entry =
    | Vis : {
        dim : 'm D.t;
        (* The reason for the dimension "snoc" here is so that some of the terms and types in these bindings can refer to other ones.  Of course it should really be only the *later* ones that can refer to the *earlier* ones, but we don't have a way to specify that in the type parameters. *)
        plus_lock : (('b, ('modality, 'mn) dim_entry) snoc, 'mode, 'modality, 'dom, 'bm) plus_lock;
        plusdim : ('m, 'n, 'mn) D.plus;
        vars : (N.zero, 'n, binder_name, 'f1) NICubeOf.t;
        bindings : ('mn, ('dom, 'bm) binding) CubeOf.t;
        hasfields : ('m, 'f2) has_fields;
        fields : (D.zero Field.t * string * ('dom, 'bm, kinetic) term, 'f2) Bwv.t;
        fplus : ('f1, 'f2, 'f) N.plus;
      }
        -> ('dom, 'modality, 'mode, 'b, 'bm, 'f, 'mn) entry
    | Invis :
        (('b, ('modality, 'n) dim_entry) snoc, 'mode, 'modality, 'dom, 'bm) plus_lock
        * ('n, ('dom, 'bm) binding) CubeOf.t
        * hints
        -> ('dom, 'modality, 'mode, 'b, 'bm, N.zero, 'n) entry

  and (_, _, _) ordered_termctx =
    | Emp : 'mode Mode.t -> ('mode, N.zero, (unit id, 'mode proj) suc) ordered_termctx
    (* I really want to call this "Snoc", but OCaml's typechecker is not properly bidirectional, so it ends up confusing such a constructor with the like-named constructor of Bwd.  *)
    | Ext :
        ('mode, 'a, 'b) ordered_termctx
        * ('dom, 'modality, 'mode, 'b, 'bm, 'x, 'n) entry
        * ('a, 'x, 'ax) N.plus
        -> ('mode, 'ax, ('b, ('modality, 'n) dim_entry) snoc) ordered_termctx
    | Lock :
        ('cod, 'a, 'b) ordered_termctx * ('dom, 'modality, 'cod) Modality.gen
        -> ('dom, 'a, ('b, 'modality lock_entry) snoc) ordered_termctx
    | Parametric_lock : ('mode, 'a, 'b) ordered_termctx -> ('mode, 'a, 'b) ordered_termctx

  and ('mode, 'a, 'b) termctx =
    | Permute : ('a, 'i) N.permute * ('mode, 'i, 'b) ordered_termctx -> ('mode, 'a, 'b) termctx
end

include Term

(* Find the name of the (n+1)st abstracted variable, where n is the length of a supplied argument list.  Doesn't "look through" branches or cobranches or into leaves. *)
let rec nth_var : type mode a b s. (mode, a, s) term -> b Bwd.t -> any_variables option =
 fun tr args ->
  match tr with
  | Lam (x, _, body) -> (
      match args with
      | Emp -> Some (Any x)
      | Snoc (args, _) -> nth_var body args)
  | _ -> None

let pi : type mode modality a.
    D.zero variables ->
    (mode, modality, a, kinetic) modal_term ->
    (mode, (a, (modality, D.zero) dim_entry) snoc, kinetic) term ->
    (mode, a, kinetic) term =
 fun x (Modal (modality, plus, dom)) cod ->
  Pi (x, Modal (modality, plus, CubeOf.singleton dom), CodCube.singleton (Cod cod))

let app fn modality al arg = App (fn, Modal (modality, al, CubeOf.singleton arg))
let appid fn mode arg = App (fn, Modal (Modality.id mode, plus_no_lock mode, CubeOf.singleton arg))

let apps fn mode args =
  List.fold_left (fun f -> app f (Modality.id mode) (plus_no_lock mode)) fn args

(* let constr name args = Constr (name, D.zero, List.map CubeOf.singleton args) *)
let field tm f = Field (tm, f, ins_zero D.zero)

module Telescope = struct
  type ('mode, 'a, 'b, 'ab) t = ('mode, 'a, 'b, 'ab) Term.tel

  let rec length : type mode a b ab. (mode, a, b, ab) t -> b Fwn.t = function
    | Emp -> Zero
    | Ext (_, _, tel) -> Suc (length tel)

  let rec pis : type mode a b ab.
      (mode, a, b, ab) t -> (mode, ab, kinetic) term -> (mode, a, kinetic) term =
   fun doms cod ->
    match doms with
    | Emp -> cod
    | Ext (x, dom, doms) ->
        pi (singleton_variables D.zero (binder_name_of_option x)) dom (pis doms cod)

  let rec lams : type mode a b ab.
      (mode, a, b, ab) t -> (mode, ab, kinetic) term -> (mode, a, kinetic) term =
   fun doms body ->
    match doms with
    | Emp -> body
    | Ext (x, Modal (modality, _, _), doms) ->
        Lam (singleton_variables D.zero (binder_name_of_option x), modality, lams doms body)
end

let rec dim_term_env : type mode a n b. (mode, a, n, b) env -> n D.t = function
  | Emp (_, n) -> n
  | Ext (e, _, _) -> dim_term_env e
  | Key { env; _ } -> dim_term_env env

let dim_entry : type dom modality mode b f n bm. (dom, modality, mode, b, bm, f, n) entry -> n D.t =
  function
  | Vis { bindings; _ } -> CubeOf.dim bindings
  | Invis (_, bindings, _) -> CubeOf.dim bindings

let plus_lock_entry : type dom modality mode b f n bm.
    (dom, modality, mode, b, bm, f, n) entry ->
    ((b, (modality, n) dim_entry) snoc, mode, modality, dom, bm) plus_lock = function
  | Vis { plus_lock; _ } -> plus_lock
  | Invis (plus_lock, _, _) -> plus_lock

let modality_entry : type dom modality mode b f n bm.
    (dom, modality, mode, b, bm, f, n) entry -> (dom, modality, mode) Modality.t =
 fun e -> plus_lock_modality (plus_lock_entry e)

module Termctx = struct
  type ('mode, 'a, 'b) ordered = ('mode, 'a, 'b) ordered_termctx
  type ('mode, 'a, 'b) t = ('mode, 'a, 'b) termctx

  let rec ordered_tctx : type mode a b. (mode, a, b) ordered_termctx -> (mode, b) Tctx.t = function
    | Emp mode -> Path (Suc (Zero, Proj mode), Unit)
    | Ext (ctx, e, _) -> Tctx.suc (ordered_tctx ctx) (Dim (modality_entry e, dim_entry e))
    | Lock (ctx, modality) -> Tctx.suc (ordered_tctx ctx) (Lock modality)
    | Parametric_lock ctx -> ordered_tctx ctx

  let tctx (Permute (_, ctx)) = ordered_tctx ctx

  let ordered_ext_let : type dom modality mode a b bm.
      (mode, a, b) ordered_termctx ->
      binder_name ->
      ((b, (modality, D.zero) dim_entry) snoc, mode, modality, dom, bm) plus_lock ->
      (dom, bm) binding ->
      (mode, a N.suc, (b, (modality, D.zero) dim_entry) snoc) ordered_termctx =
   fun ctx x plus_lock b ->
    Ext
      ( ctx,
        Vis
          {
            dim = D.zero;
            plus_lock;
            plusdim = D.plus_zero D.zero;
            vars = NICubeOf.singleton x;
            bindings = CubeOf.singleton b;
            hasfields = No_fields;
            fields = Emp;
            fplus = Zero;
          },
        Suc Zero )

  let ext_let (Permute (p, ctx)) al xs b =
    let ctx = ordered_ext_let ctx al xs b in
    Permute (Insert (p, Top), ctx)

  let ext (Permute (p, ctx)) al xs ty =
    let ctx = ordered_ext_let ctx al xs { ty; tm = None } in
    Permute (Insert (p, Top), ctx)

  let rec ordered_mode : type mode a b. (mode, a, b) ordered_termctx -> mode Mode.t = function
    | Emp mode -> mode
    | Ext (ctx, _, _) -> ordered_mode ctx
    | Lock (_, lock) -> Modality.Gen.src lock
    | Parametric_lock ctx -> ordered_mode ctx

  let mode (Permute (_, ctx)) = ordered_mode ctx

  (* Remove *all* locks at the end of a context. *)

  type (_, _, _) ordered_remove_locks =
    | Ordered_remove_locks :
        ('cod, 'a, 'b) ordered * ('b, 'cod, 'modality, 'mode, 'bc) plus_lock
        -> ('mode, 'a, 'bc) ordered_remove_locks

  let rec ordered_remove_locks : type mode a bc.
      (mode, a, bc) ordered -> (mode, a, bc) ordered_remove_locks =
   fun ctx ->
    match ctx with
    | Emp _ | Ext (_, _, _) -> Ordered_remove_locks (ctx, plus_no_lock (ordered_mode ctx))
    | Parametric_lock ctx ->
        (* Not going to think about whether this is quite correct, since Parametric_lock is going away the first chance we get. *)
        ordered_remove_locks ctx
    | Lock (ctx, g) ->
        let (Ordered_remove_locks (ctx, plus)) = ordered_remove_locks ctx in
        Ordered_remove_locks (ctx, plus_lock_suc plus g)

  type (_, _) remove_locks =
    | Remove_locks :
        ('cod, 'a, 'b) t * ('b, 'cod, 'modality, 'mode, 'bc) plus_lock
        -> ('mode, 'bc) remove_locks

  let remove_locks : type mode a bc. (mode, a, bc) t -> (mode, bc) remove_locks =
   fun (Permute (p, ctx)) ->
    let (Ordered_remove_locks (ctx, plus)) = ordered_remove_locks ctx in
    Remove_locks (Permute (p, ctx), plus)

  (* let ext (Permute (p, ctx)) xs ty =
       let ctx = ordered_ext_let ctx xs { ty; tm = None } in
       Permute (Insert (p, Top), ctx) *)
end

(* Merge the binder names stored in a termctx, which carry display hints for anonymous variables, into a flat scope of raw variable names such as is stored for a hole.  Raw names that are present take precedence; absent ones pick up the hints (if any) from the corresponding termctx binder.  This is used when generating display names for the context of a hole. *)
let rec ordered_hole_vars : type mode a b.
    (mode, a, b) ordered_termctx -> (string option, a) Bwv.t -> (binder_name, a) Bwv.t =
 fun ctx vars ->
  match ctx with
  | Emp _ ->
      let Emp = vars in
      Emp
  | Lock (ctx, _) -> ordered_hole_vars ctx vars
  | Parametric_lock ctx -> ordered_hole_vars ctx vars
  | Ext (ctx, entry, af) -> (
      let vars, xs = Bwv.unappend af vars in
      let rest = ordered_hole_vars ctx vars in
      match entry with
      | Invis _ ->
          let Zero = af in
          rest
      | Vis { vars = cube; fplus; _ } ->
          let xs, fs = Bwv.unappend fplus xs in
          (* First merge the raw names into the cube of binder names, consuming the Bwv from the right so that its indices match the cube's. *)
          let module TR = NICubeOf.Traverse (struct
            type 'a t = (string option, 'a) Bwv.t
          end) in
          let merge : type left m n.
              (m, n) sface ->
              (left, m, binder_name) NFamOf.t ->
              (string option, left N.suc) Bwv.t ->
              (string option, left) Bwv.t * (left, m, binder_name) NFamOf.t =
           fun _ (NFamOf y) (Snoc (xs, x)) ->
            match x with
            | Some x -> (xs, NFamOf (`Named x))
            | None -> (
                match y with
                | `Anon _ -> (xs, NFamOf y)
                | `Named _ -> (xs, NFamOf (`Anon no_hints))) in
          let _, merged = TR.fold_map_right { foldmap = (fun fb y xs -> merge fb y xs) } cube xs in
          (* Then convert the merged cube of binder names back into a Bwv. *)
          let module TL = NICubeOf.Traverse (struct
            type 'a t = (binder_name, 'a) Bwv.t
          end) in
          let _, xs =
            TL.fold_map_left
              { foldmap = (fun _ acc (NFamOf y) -> (NFamOf y, Snoc (acc, y))) }
              Emp merged in
          (* Field variables have no hints. *)
          let fs = Bwv.map binder_name_of_option fs in
          Bwv.bappend af rest (Bwv.bappend fplus xs fs))

let hole_vars : type mode a b.
    (mode, a, b) termctx -> (string option, a) Bwv.t -> (binder_name, a) Bwv.t =
 fun (Permute (p, ctx)) vars ->
  Bwv.permute (ordered_hole_vars ctx (Bwv.permute vars p)) (N.perm_inv p)
