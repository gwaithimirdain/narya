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
          ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
          * ('mode, ('a, ('modality, 'k) dim_entry) snoc, kinetic) Term.term
          -> ('n, 'dom * 'modality * 'mode * 'a) t
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

  module FieldtypeFam : sig
    type (_, _) t =
      | Fieldtype :
          ('r, 'b, 'rb, 'mode) plusmap * ('mode, 'rb, kinetic) Term.term
          -> ('r, 'mode * 'b) t
  end

  module FieldtypePbijmap : module type of Pbijmap (FieldtypeFam)

  module Codatafield : sig
    type (_, _, _, _, _, _, _, _, _) data =
      | Lower :
          ('gmode, ('ag, ('f, 'n) dim_entry) snoc, kinetic) Term.term
          -> (D.zero, 'mode, 'f, 'gmode, 'a, 'ag, 'm, 'n, 'et) data
      | Higher :
          ('gmode, 'd, 'ag) Term.termctx
          * ('m, 'i, 'gmode * ('ag, ('f, 'm) dim_entry) snoc) FieldtypePbijmap.t
          -> ('i, 'mode, 'f, 'gmode, 'a, 'ag, 'm, 'm, no_eta) data

    type (_, _) t =
      | Codatafield :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('a, 'mode, 'g, 'gmode, 'ag) plus_lock
          * ('i, 'mode, 'f, 'gmode, 'a, 'ag, 'm, 'n, 'et) data
          -> ('i, 'mode * 'a * 'm * 'n * 'et) t
  end

  module CodatafieldAbwd : module type of Field.Abwd (Codatafield)

  module Structfield : sig
    type (_, _) t =
      | Lower :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('a, 'mode, 'g, 'gmode, 'ag) plus_lock
          * ('gmode, 'ag, 's) Term.term
          * [ `Labeled | `Unlabeled ]
          -> (D.zero, 'mode * ('n * 'a * 's * 'et)) t
      | Higher :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('a, 'mode, 'g, 'gmode, 'ag) plus_lock
          * ('n, 'i, 'gmode * 'ag) PlusPbijmap.t
          -> ('i, 'mode * ('n * 'a * potential * no_eta)) t
      | LazyHigher :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('a, 'mode, 'g, 'gmode, 'ag) plus_lock
          * ('n, 'i, 'gmode * 'ag) PlusPbijmap.t Lazy.t
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
        ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
        * ('a, 'mode, 'modality, 'dom, 'am) plus_lock
        * ('k, ('dom, 'am, 's) Term.term) CubeOf.t
        -> ('n, 'mode, 'a, 's) any_modal_term_cube

  type (_, _, _) term =
    | Var : ('mode, 'a) index -> ('mode, 'a, kinetic) term
    | Const : Constant.t -> ('mode, 'a, kinetic) term
    | Meta : ('mode, 'x, 'b, 'l) Meta.t * 's energy -> ('mode, 'b, 's) term
    | MetaEnv : ('mode, 'x, 'b, 's) Meta.t * ('mode, 'a, 'n, 'b) env -> ('mode, 'a, kinetic) term
    | Field :
        's energy * ('mode, 'f, 'a, 's) modal_term * 'i Field.t * ('n, 't, 'i) insertion
        -> ('mode, 'a, 's) term
    | UU : 'mode Mode.t * 'n D.t -> ('mode, 'a, kinetic) term
    | Inst :
        's energy * ('mode, 'a, 's) term * ('m, 'n, 'mn, ('mode, 'a, kinetic) term) TubeOf.t
        -> ('mode, 'a, 's) term
    | Pi : ('k, 'n, 'dom, 'modality, 'mode, 'a) pi_args -> ('mode, 'a, kinetic) term
    | App :
        's energy
        * ('mode, 'a, 's) term
        * 'm D.t
        * ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim
        * ('n, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube
        -> ('mode, 'a, 's) term
    | Constr :
        Constr.t * 'n D.t * ('n, 'mode, 'a, kinetic) any_modal_term_cube list
        -> ('mode, 'a, kinetic) term
    | Act :
        's energy
        * ('mode, 'a, 's) term
        * ('m, 'n) deg
        * ([ `Type | `Function | `Other ] * [ `Canonical | `Other ])
        -> ('mode, 'a, 's) term
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
        'k variables
        * 'n D.t
        * ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
        * ('mode, ('a, ('modality, 'k) dim_entry) snoc, 's) Term.term
        -> ('mode, 'a, 's) term
    | Struct : ('mode, 'n, 'a, 's, 'et) struct_args -> ('mode, 'a, 's) term
    | Match : {
        window : ('dom, 'window, 'mode) Modality.t;
        plus_lock : ('a, 'mode, 'window, 'dom, 'aw) plus_lock;
        tm : ('dom, 'aw, kinetic) term;
        dim : 'n D.t;
        motive : ('mode, 'a) match_motive option;
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

  and ('k, 'n, 'dom, 'modality, 'mode, 'a) pi_args = {
    x : 'k variables;
    filter : ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim;
    doms : ('k, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube;
    cods : ('n, 'dom * 'modality * 'mode * 'a) CodCube.t;
  }

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

  and ('mode, 'a) match_motive =
    [ `Family of ('mode, 'a, kinetic) term | `Type of ('mode, 'a, kinetic) term ]

  and (_, _) canonical =
    | Data : {
        indices : 'i Fwn.t;
        evaldim : 'm D.t;
        constrs : (Constr.t, ('mode, 'a, kinetic) term) Abwd.t;
        discrete : [ `Yes | `Maybe | `No ];
        recursive : Positivity.recursion;
        hints : hints;
        tyfam : ('mode, 'a, kinetic) term;
      }
        -> ('mode, 'a) canonical
    | Codata : ('mode, 'm, 'n, 'mn, 'a, 'nh, 'ha, 'et) codata_args -> ('mode, 'a) canonical

  and ('mode, 'm, 'n, 'mn, 'a, 'nh, 'ha, 'et) codata_args = {
    eta : (potential, 'et) eta;
    opacity : opacity;
    hints : hints;
    evaldim : 'm D.t;
    dim : 'n D.t;
    plusdim : ('m, 'n, 'mn) D.plus;
    fields : ('mode * 'a * 'm * 'mn * 'et) CodatafieldAbwd.t;
    fibrancy : ('mode, 'm, 'n, 'n, 'nh, 'a, 'ha, 'et) codata_fibrancy option;
    is_glue : ('mode, 'n, 'a, 'et) is_glue option;
  }

  and ('mode, 'm, 'g, 'n, 'nh, 'b, 'hb, 'et) codata_fibrancy = {
    evaldim : ('m, D.zero) Eq.t;
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

  and (_, _, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'a, 'n, 'mode emp) env
    | Ext : {
        env : ('mode, 'a, 'n, 'b) env;
        filtered : ('dom, 'modality, 'mode, 'k, 'k) Modality.filter_dim;
        filter : ('dom, 'modality, 'mode, 'm, 'n) Modality.filter_dim;
        plus : ('m, 'k, 'mk) D.plus;
        values : ('mk, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube;
      }
        -> ('mode, 'a, 'n, ('b, ('modality, 'k) dim_entry) snoc) env
    | Key : {
        env : ('cod, 'a, 'n, 'b) env;
        cell : ('mode, 'mu, 'nu, 'cod) Modalcell.t;
        plus_tgt : ('a, 'cod, 'nu, 'mode, 'ac) plus_with_locks;
        plus_src : ('b, 'cod, 'mu, 'mode, 'bmu) plus_lock;
      }
        -> ('mode, 'ac, 'n, 'bmu) env
    | Prekey : {
        env : ('mode, 'asrc, 'n, 'b) env;
        cell : ('mode, 'pmu, 'pnu, 'pcod) Modalcell.t;
        plus_src : ('a, 'pcod, 'pmu, 'mode, 'asrc) plus_lock;
        plus_tgt : ('a, 'pcod, 'pnu, 'mode, 'atgt) plus_with_locks;
      }
        -> ('mode, 'atgt, 'n, 'b) env

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
        filter : ('dom, 'modality, 'mode, 'mn, 'mn) Modality.filter_dim;
        vars : (N.zero, 'n, binder_name, 'f1) NICubeOf.t;
        bindings : ('mn, ('dom, 'bm) binding) CubeOf.t;
        hasfields : ('m, 'f2) has_fields;
        fields : (D.zero Field.t * string * ('dom, 'bm, kinetic) term, 'f2) Bwv.t;
        fplus : ('f1, 'f2, 'f) N.plus;
      }
        -> ('dom, 'modality, 'mode, 'b, 'bm, 'f, 'mn) entry
    | Invis : {
        plus_lock : (('b, ('modality, 'n) dim_entry) snoc, 'mode, 'modality, 'dom, 'bm) plus_lock;
        filter : ('dom, 'modality, 'mode, 'n, 'n) Modality.filter_dim;
        bindings : ('n, ('dom, 'bm) binding) CubeOf.t;
        hints : hints;
      }
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
    | Weaken :
        ('mode, 'a, 'b) ordered_termctx * Reporter.Code.t
        -> ('mode, 'a N.suc, 'b) ordered_termctx

  and ('mode, 'a, 'b) termctx =
    | Permute : ('a, 'i) N.permute * ('mode, 'i, 'b) ordered_termctx -> ('mode, 'a, 'b) termctx
end = struct
  module CodFam = struct
    type ('k, _) t =
      | Cod :
          ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
          * ('mode, ('a, ('modality, 'k) dim_entry) snoc, kinetic) Term.term
          -> ('n, 'dom * 'modality * 'mode * 'a) t
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

  (* One instance of the type of a higher codata field: a term in the context degenerated by the instance's remaining dimensions, together with the plus-map witnessing that degeneration.  (Compare PlusFam, which is the same thing for the *components* of a comatch, which are potential rather than kinetic and may be missing.) *)
  module FieldtypeFam = struct
    type (_, _) t =
      | Fieldtype :
          ('r, 'b, 'rb, 'mode) plusmap * ('mode, 'rb, kinetic) Term.term
          -> ('r, 'mode * 'b) t
  end

  module FieldtypePbijmap = Pbijmap (FieldtypeFam)

  module Codatafield = struct
    (* A codata field is parametrized by an adjunction in the mode 2-category.  Its type is a term in the context locked by the right adjoint and then extended by the self variable annotated by the left adjoint, hence lives at the right adjoint's source mode.  (By the adjunction, this is equivalent to extending by an identity-annotated self variable and then locking by the right adjoint: a key from the self variable's annotation to the locks to its right is 1 ⇒ g·ν in the latter presentation and f ⇒ ν in the former, and these are interderivable using the unit and counit.  We use this presentation since it is the one from Multimodal Adjoint Type Theory.)  Ordinary non-modal fields are the special case of the identity adjunction, where the lock is trivial and the annotation is the identity.

       The family is indexed by two dimensions of the codatatype: its evaluation dimension 'm, and the dimension 'n of the self variable, which is the evaluation dimension plus the intrinsic (Gel) dimension.  A codatatype produced by typechecking has evaluation dimension zero, so that its self variable has just the intrinsic dimension; the general case arises from the readback of a codatatype *value*, which is displayed by "about" (see codata_args).

       A higher field of intrinsic dimension i has one type per instance, i.e. per partial bijection between the codatatype's evaluation dimension and i, so its types are stored in a pbijmap.  The instance at a partial bijection with 'r remaining dimensions has its type in the locked and self-extended context degenerated by those 'r dimensions (which is what the plus-map in FieldtypeFam records), since that is where such an instance is checked.  In particular, when the evaluation dimension is zero there is exactly one instance, with all i dimensions remaining: the declaration form "x .fld.e… : A", whose type is checked in the context degenerated by the whole of i, so that its self variable is an i-dimensional cube.  Since the self variable is added before the degeneration, its dimension there is exactly i.

       A codatatype with a higher field must have intrinsic dimension zero (Gel-like codatatypes can't have higher fields), which is why the two dimensions coincide in Higher: the self variable and the instances are indexed by the same dimension.  This is necessary to ensure statically when evaluating a typechecked field, where we know that the evaluation dimension is zero, that the Gel-dimension is also zero.  In the lower-dimensional case, we don't ensure here that n is m plus anything because we don't need it. *)

    type (_, _, _, _, _, _, _, _, _) data =
      | Lower :
          ('gmode, ('ag, ('f, 'n) dim_entry) snoc, kinetic) Term.term
          -> (D.zero, 'mode, 'f, 'gmode, 'a, 'ag, 'm, 'n, 'et) data
      | Higher :
          (* The context that the field's type closure is evaluated over, as a termctx, needed to eval-readback that environment when degenerating it to check the field at a nontrivial partial bijection.  Note this is the *locked* context, without the self variable: the self variable is supplied to the field type after the degeneration, not carried through it inside the environment. *)
          ('gmode, 'd, 'ag) Term.termctx
          * ('m, 'i, 'gmode * ('ag, ('f, 'm) dim_entry) snoc) FieldtypePbijmap.t
          -> ('i, 'mode, 'f, 'gmode, 'a, 'ag, 'm, 'm, no_eta) data

    type (_, _) t =
      | Codatafield :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('a, 'mode, 'g, 'gmode, 'ag) plus_lock
          * ('i, 'mode, 'f, 'gmode, 'a, 'ag, 'm, 'n, 'et) data
          -> ('i, 'mode * 'a * 'm * 'n * 'et) t
  end

  module CodatafieldAbwd = Field.Abwd (Codatafield)

  module Structfield = struct
    (* Lazy fields are not allowed in ordinary terms, because a term is supposed to be a completed data object that can be, for instance, serialized to a file and reloaded.  But when we use this to store fibrancy fields, which are recomputed on evaluation and are corecursively infinite, we have to allow laziness.  *)
    type (_, _) t =
      (* Like a codata field, a lower struct field is parametrized by an adjunction: the supplied term lives behind a lock by the right adjoint.  Ordinary non-modal fields use the identity adjunction. *)
      | Lower :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('a, 'mode, 'g, 'gmode, 'ag) plus_lock
          * ('gmode, 'ag, 's) Term.term
          * [ `Labeled | `Unlabeled ]
          -> (D.zero, 'mode * ('n * 'a * 's * 'et)) t
      | Higher :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('a, 'mode, 'g, 'gmode, 'ag) plus_lock
          * ('n, 'i, 'gmode * 'ag) PlusPbijmap.t
          -> ('i, 'mode * ('n * 'a * potential * no_eta)) t
      | LazyHigher :
          ('mode, 'f, 'g, 'gmode) Modalcell.adjunction
          * ('a, 'mode, 'g, 'gmode, 'ag) plus_lock
          * ('n, 'i, 'gmode * 'ag) PlusPbijmap.t Lazy.t
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

  (* Similarly, but when we don't know what the modality might be, and the filtering is included. *)
  type (_, _, _, _) any_modal_term_cube =
    | Modal :
        ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
        * ('a, 'mode, 'modality, 'dom, 'am) plus_lock
        * ('k, ('dom, 'am, 's) Term.term) CubeOf.t
        -> ('n, 'mode, 'a, 's) any_modal_term_cube

  type (_, _, _) term =
    (* Most term-formers only appear in kinetic (ordinary) terms. *)
    | Var : ('mode, 'a) index -> ('mode, 'a, kinetic) term
    | Const : Constant.t -> ('mode, 'a, kinetic) term
    | Meta : ('mode, 'x, 'b, 'l) Meta.t * 's energy -> ('mode, 'b, 's) term
    (* Normally, checked metavariables don't require an environment attached, but they do when they arise by readback from a value metavariable. *)
    | MetaEnv : ('mode, 'x, 'b, 's) Meta.t * ('mode, 'a, 'n, 'b) env -> ('mode, 'a, kinetic) term
    (* A field projection.  For a modal field, the term being projected lives behind a lock by the left adjoint of the field's adjunction; for ordinary fields that modality is the identity. *)
    | Field :
        's energy * ('mode, 'f, 'a, 's) modal_term * 'i Field.t * ('n, 't, 'i) insertion
        -> ('mode, 'a, 's) term
    | UU : 'mode Mode.t * 'n D.t -> ('mode, 'a, kinetic) term
    (* Normally an instantiation can only be kinetic, but we permit potential ones to be the values of display-only readback of instantiated canonicals. *)
    | Inst :
        's energy * ('mode, 'a, 's) term * ('m, 'n, 'mn, ('mode, 'a, kinetic) term) TubeOf.t
        -> ('mode, 'a, 's) term
    | Pi : ('k, 'n, 'dom, 'modality, 'mode, 'a) pi_args -> ('mode, 'a, kinetic) term
    (* Normally an application can only be kinetic, but we permit potential ones to be the values of display-only readback of indexed datatypes applied to their indices. *)
    | App :
        's energy
        * ('mode, 'a, 's) term
        * 'm D.t
        * ('dom, 'modality, 'mode, 'n, 'm) Modality.filter_dim
        * ('n, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube
        -> ('mode, 'a, 's) term
    | Constr :
        Constr.t * 'n D.t * ('n, 'mode, 'a, kinetic) any_modal_term_cube list
        -> ('mode, 'a, kinetic) term
    | Act :
        's energy
        * ('mode, 'a, 's) term
        * ('m, 'n) deg
        * ([ `Type | `Function | `Other ] * [ `Canonical | `Other ])
        -> ('mode, 'a, 's) term
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
        'k variables
        * 'n D.t
        * ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim
        * ('mode, ('a, ('modality, 'k) dim_entry) snoc, 's) Term.term
        -> ('mode, 'a, 's) term
    | Struct : ('mode, 'n, 'a, 's, 'et) struct_args -> ('mode, 'a, 's) term
    (* Matches can only appear in potential terms.  The dimension 'n is the substitution dimension of the type of the variable being matched against.  The term, and its datatype, live at a domain mode, and the window modality maps that to some other mode where the branches live. *)
    | Match : {
        window : ('dom, 'window, 'mode) Modality.t;
        plus_lock : ('a, 'mode, 'window, 'dom, 'aw) plus_lock;
        tm : ('dom, 'aw, kinetic) term;
        dim : 'n D.t;
        (* What the match records of its type; see match_motive.  Evaluation never needs it, since the branch it selects carries its own body. *)
        motive : ('mode, 'a) match_motive option;
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

  and ('k, 'n, 'dom, 'modality, 'mode, 'a) pi_args = {
    x : 'k variables;
    filter : ('dom, 'modality, 'mode, 'k, 'n) Modality.filter_dim;
    doms : ('k, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube;
    cods : ('n, 'dom * 'modality * 'mode * 'a) CodCube.t;
  }

  and ('mode, 'n, 'a, 's, 'et) struct_args = {
    dim : 'n D.t;
    fields : ('mode * ('n * 'a * 's * 'et)) StructfieldAbwd.t;
    eta : ('s, 'et) eta;
    energy : 's energy;
  }

  (* A branch of a match binds a number of new variables.  If it is a higher-dimensional match, then each of those "variables" is actually a full cube of variables.  In addition, its context must be permuted to put those new variables before the existing variables that are now defined in terms of them.  Finally, each of the variables might be annotated by a different modality, so we include a list of such modalities and make it into a tctx extension that all have the same dimension. *)
  (* The pattern-variable display names are carried inside the "annotate" witness (one per variable, in VarAnnote/VarAnnotator), so unparse.ml can recover them when displaying a match branch ("about pred"). *)
  and (_, _, _) branch =
    | Branch : {
        (* The annotations must be those given to the constructor arguments, postcomposed by the window modality *)
        annotate : ('n, 'mode, 'annotations, 'mode, 'mode, 'b, 'mode) VarAnnotate.fwd_t;
        comp : ('mode, 'b, 'mode, 'a, unit, 'ab) Tctx.bcomp;
        perm : ('c, 'ab) permute;
        tm : ('mode, 'c, potential) term;
      }
        -> ('mode, 'a, 'n) branch

  (* What a match records of its type, so that readback can recover it when the match is stuck and something has been done to its result -- applied to an argument, or projected -- so that the type readback is handed is that of the whole spine rather than of the match.  A match with an explicit dependent motive stores that motive, a type family over the datatype's indices and the datatype itself, to be applied to a branch's indices and constructor.  A non-dependent match checks all its branches at one type (perhaps synthesizing the type from one of them) and stores that, which is both the type of the match and the type of every branch.  A variable match refines the context instead, and stores neither. *)
  and ('mode, 'a) match_motive =
    [ `Family of ('mode, 'a, kinetic) term | `Type of ('mode, 'a, kinetic) term ]

  (* A canonical type is either a datatype or a codatatype/record. *)
  and (_, _) canonical =
    (* A datatype stores its family of constructors, whether it is discrete, whether it has recursive constructors, and also its number of indices.  (The former two are not determined in the latter if there happen to be zero constructors). *)
    | Data : {
        indices : 'i Fwn.t;
        (* The dimension the datatype was evaluated at, exactly as for the [evaldim] of a codatatype: zero for one produced by typechecking, and positive only for the display-only readback of a degenerated datatype value, whose constructors then store higher-dimensional pi-types.  Evaluation ignores it, taking the dimension from its environment instead; it is stored so that the unparser can display the dimension on the "data" keyword. *)
        evaldim : 'm D.t;
        (* Each constructor is stored as its full function-type: the iterated (modal, zero-dimensional) pi-type over its argument telescope whose codomain is the datatype family applied to the parameters and indices.  It is walked on demand, evaluating and introducing the arguments (e.g. by ext_pi in match typechecking) to reach the codomain, off which the index values are read; its arity and argument names alone are available more cheaply via Telescope.pi_arity and Telescope.pi_names.  For a non-indexed datatype, where the user need not write an output type, the codomain is synthesized as the datatype applied to its parameters.  The readback of a higher-dimensionally degenerated datatype stores a higher-dimensional pi-type here; that is used only for display and is not re-evaluable. *)
        constrs : (Constr.t, ('mode, 'a, kinetic) term) Abwd.t;
        discrete : [ `Yes | `Maybe | `No ];
        recursive : Positivity.recursion;
        (* Variable-name hints, for displaying anonymous variables of this type. *)
        hints : hints;
        (* The datatype applied to its parameters, with its indices abstracted (e.g. "Vec A").  This is read back at checking time, where the current head and its argument spine (the parameters) are available in the "potential" status; then at evaluation time it lets us fill in the value-level [tyfam] directly, rather than back-patching it once the enclosing neutral is observed.  (Its type is not stored: it is recovered from the neutral this evaluates to, which carries it fully-instantiated at the current dimension.) *)
        tyfam : ('mode, 'a, kinetic) term;
      }
        -> ('mode, 'a) canonical
    | Codata : ('mode, 'm, 'n, 'mn, 'a, 'nh, 'ha, 'et) codata_args -> ('mode, 'a) canonical

  and ('mode, 'm, 'n, 'mn, 'a, 'nh, 'ha, 'et) codata_args = {
    (* An eta flag and its opacity *)
    eta : (potential, 'et) eta;
    opacity : opacity;
    (* Variable-name hints, for displaying anonymous variables of this type. *)
    hints : hints;
    (* An evaluation dimension, an intrinsic dimension (like Gel), and their sum, which is the dimension of the self variable.  Typechecking only ever produces codatatypes of evaluation dimension zero, whose self variable therefore has just the intrinsic dimension; a positive evaluation dimension arises only from the readback of a codatatype *value* that has been substituted to a higher dimension, which is display-only (see below). *)
    evaldim : 'm D.t;
    dim : 'n D.t;
    plusdim : ('m, 'n, 'mn) D.plus;
    (* A family of fields, each with a type that depends on one additional variable belonging to the codatatype itself (usually by way of its previous fields).  We retain the order of the fields by storing them in an Abwd rather than a Map so as to enable positional access as well as named access.  A higher field carries one type per instance, indexed by the evaluation dimension; see Codatafield. *)
    fields : ('mode * 'a * 'm * 'mn * 'et) CodatafieldAbwd.t;
    (* We partially compute the fibrancy fields at typechecking time, although we don't finish the computation until we need it.  Since the fibrancy fields include those of all the higher identity types, if we did all the computation eagerly it would be infinite, and if we made it Lazy in the naive way then it wouldn't be marshalable.  This is an option because the readback of a codatatype value (for display only) carries no fibrancy. *)
    fibrancy : ('mode, 'm, 'n, 'n, 'nh, 'a, 'ha, 'et) codata_fibrancy option;
    (* Fibrancy of glue-types is computed separately and stored, so we remember whether this is a glue-type. *)
    is_glue : ('mode, 'n, 'a, 'et) is_glue option;
  }

  and ('mode, 'm, 'g, 'n, 'nh, 'b, 'hb, 'et) codata_fibrancy = {
    (* We have fibrancy only when the evaluation dimension is zero. *)
    evaldim : ('m, D.zero) Eq.t;
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

  (* A version of an environment that involves terms rather than values.  Used mainly when reading back metavariables.  The first argument is the mode, the second is the checked-length of the context *in* which the environment is defined (its domain, as a context morphism), the third is its dimension, and the fourth is the checked-length of the context of types of the values in the environment (its codomain, as a context morphism).  *)
  and (_, _, _, _) env =
    | Emp : 'mode Mode.t * 'n D.t -> ('mode, 'a, 'n, 'mode emp) env
    | Ext : {
        env : ('mode, 'a, 'n, 'b) env;
        filtered : ('dom, 'modality, 'mode, 'k, 'k) Modality.filter_dim;
        filter : ('dom, 'modality, 'mode, 'm, 'n) Modality.filter_dim;
        plus : ('m, 'k, 'mk) D.plus;
        values : ('mk, 'dom, 'modality, 'mode, 'a, kinetic) modal_term_cube;
      }
        -> ('mode, 'a, 'n, ('b, ('modality, 'k) dim_entry) snoc) env
    (* There is a decision to be made here about how to deal with keys in a term environment.  The problem is that the part of the environment to the left of a key must be defined in a context that has the locks corresponding to the codomain of that key removed, along with everything interspersed with them and to their right.  But simply removing variables from the context fubars the De Bruijn indices.  We could replace the removed indices in the context by a placeholder that extends out its length while containing no data.  Instead, we choose to allow the domain length of a term environment to increase when we pass a key.  This means when working with such environments we must shrink the domain context when we pass a key. *)
    | Key : {
        env : ('cod, 'a, 'n, 'b) env;
        cell : ('mode, 'mu, 'nu, 'cod) Modalcell.t;
        plus_tgt : ('a, 'cod, 'nu, 'mode, 'ac) plus_with_locks;
        plus_src : ('b, 'cod, 'mu, 'mode, 'bmu) plus_lock;
      }
        -> ('mode, 'ac, 'n, 'bmu) env
    (* A prekey acts by a key cell on all the values of a term environment (the term-level analogue of Value.Prekey).  It doesn't change the mode or the codomain context, but unlike its value-level analogue it does mediate the domain context: the environment inside is valid in a context locked by the cell's vertical source, while the whole is valid in a context locked by its vertical target (over a common base), as when a parametric locker's counit has discharged the locks that a metavariable was created behind. *)
    | Prekey : {
        env : ('mode, 'asrc, 'n, 'b) env;
        cell : ('mode, 'pmu, 'pnu, 'pcod) Modalcell.t;
        plus_src : ('a, 'pcod, 'pmu, 'mode, 'asrc) plus_lock;
        plus_tgt : ('a, 'pcod, 'pnu, 'mode, 'atgt) plus_with_locks;
      }
        -> ('mode, 'atgt, 'n, 'b) env

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
        filter : ('dom, 'modality, 'mode, 'mn, 'mn) Modality.filter_dim;
        vars : (N.zero, 'n, binder_name, 'f1) NICubeOf.t;
        bindings : ('mn, ('dom, 'bm) binding) CubeOf.t;
        hasfields : ('m, 'f2) has_fields;
        fields : (D.zero Field.t * string * ('dom, 'bm, kinetic) term, 'f2) Bwv.t;
        fplus : ('f1, 'f2, 'f) N.plus;
      }
        -> ('dom, 'modality, 'mode, 'b, 'bm, 'f, 'mn) entry
    | Invis : {
        plus_lock : (('b, ('modality, 'n) dim_entry) snoc, 'mode, 'modality, 'dom, 'bm) plus_lock;
        filter : ('dom, 'modality, 'mode, 'n, 'n) Modality.filter_dim;
        bindings : ('n, ('dom, 'bm) binding) CubeOf.t;
        hints : hints;
      }
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
    (* A weakening entry increases the raw length by one but stores no checked variables, only a Code.t to raise on lookup of the dataless variable.  Mirrors Ctx.Ordered.Weaken. *)
    | Weaken :
        ('mode, 'a, 'b) ordered_termctx * Reporter.Code.t
        -> ('mode, 'a N.suc, 'b) ordered_termctx

  and ('mode, 'a, 'b) termctx =
    | Permute : ('a, 'i) N.permute * ('mode, 'i, 'b) ordered_termctx -> ('mode, 'a, 'b) termctx
end

include Term

(* The type of a higher codata field of a codatatype of evaluation dimension zero, which is what typechecking produces: there is exactly one instance, namely the declaration form "x .fld.e… : A", whose type lives in the context degenerated by the whole intrinsic dimension of the field.  (A codatatype of positive evaluation dimension, which arises only from readback for display, has one instance per partial bijection instead.) *)
let declared_fieldtype : type i gmode b.
    (D.zero, i, gmode * b) FieldtypePbijmap.t -> (i, gmode * b) FieldtypeFam.t =
 fun tys ->
  FieldtypePbijmap.find (Pbij (ins_zero D.zero, shuffle_zero (FieldtypePbijmap.intrinsic tys))) tys

(* Conversely, assemble that unique instance into a pbijmap, when checking a higher field declaration. *)
let singleton_fieldtype : type i gmode b rb.
    i D.t ->
    (i, b, rb, gmode) plusmap ->
    (gmode, rb, kinetic) term ->
    (D.zero, i, gmode * b) FieldtypePbijmap.t =
 fun i plusmap ty ->
  FieldtypePbijmap.build D.zero i
    {
      build =
        (fun (type r) (pbij : (D.zero, i, r) pbij) : (r, gmode * b) FieldtypeFam.t ->
          let Eq = eq_of_zero_pbij pbij in
          Fieldtype (plusmap, ty));
    }

(* Find the name of the (n+1)st abstracted variable, where n is the length of a supplied argument list.  Doesn't "look through" branches or cobranches or into leaves. *)
let rec nth_var : type mode a b s. (mode, a, s) term -> b Bwd.t -> any_variables option =
 fun tr args ->
  match tr with
  | Lam (x, _, _, body) -> (
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
  let filter = Modality.filter_zero modality in
  Pi
    {
      x;
      filter;
      doms = Modal (modality, plus, CubeOf.singleton dom);
      cods = CodCube.singleton (Cod (filter, cod));
    }

let app fn modality al arg =
  App
    (Kinetic, fn, D.zero, Modality.filter_zero modality, Modal (modality, al, CubeOf.singleton arg))

let appid fn mode arg =
  App
    ( Kinetic,
      fn,
      D.zero,
      Modality.filter_id mode D.zero,
      Modal (Modality.id mode, plus_no_lock mode, CubeOf.singleton arg) )

let apps fn mode args =
  List.fold_left (fun f -> app f (Modality.id mode) (plus_no_lock mode)) fn args

(* let constr name args = Constr (name, D.zero, List.map CubeOf.singleton args) *)

(* A non-modal field projection, whose lock is the identity. *)
let modal_id : type mode a s.
    mode Mode.t -> (mode, a, s) term -> (mode, mode Modality.id, a, s) modal_term =
 fun mode tm -> Modal (Modality.id mode, plus_no_lock mode, tm)

let field mode tm f = Field (Kinetic, modal_id mode tm, f, ins_zero D.zero)

(* A telescope is a list of types, each dependent on the previous ones.  Note that 'a and 'ab are lists of dimensions, but 'b is just a forwards natural number counting the number of *zero-dimensional* variables added to 'a to get 'ab.  The variables bound in a telescope are all zero-dimensional, but they can be nontrivially modally annotated.  *)
module Telescope = struct
  type ('mode, 'a, 'b, 'ab) t =
    | Emp : ('mode, 'a, Fwn.zero, 'a) t
    | Ext :
        string option
        * ('mode, 'modality, 'a, kinetic) modal_term
        * ('mode, ('a, ('modality, D.zero) dim_entry) snoc, 'b, 'ab) t
        -> ('mode, 'a, 'b Fwn.suc, 'ab) t

  let rec pis : type mode a b ab.
      (mode, a, b, ab) t -> (mode, ab, kinetic) term -> (mode, a, kinetic) term =
   fun doms cod ->
    match doms with
    | Emp -> cod
    | Ext (x, dom, doms) ->
        pi (singleton_variables D.zero (binder_name_of_option x)) dom (pis doms cod)
end

(* Count the number of zero-dimensional pi-types on the front of a term, i.e. the length of the argument telescope of the constructor whose function-type this is, without reconstructing the telescope.  Used to determine a datatype constructor's arity from its stored function-type.  We peel only zero-dimensional pis: a dimension-killing modality can have a zero-dimensional domain cube on a positive-dimensional pi, which must not be counted, and the codomain of a higher pi is not a constructor argument. *)
let rec pi_arity : type mode a. (mode, a, kinetic) term -> Fwn.wrapped = function
  | Pi { x = _; filter; doms = Modal (modality, _, _); cods } -> (
      match D.compare_zero (CodCube.dim cods) with
      | Pos _ -> Wrap Zero
      | Zero ->
          let Eq = Modality.filter_uniq filter (Modality.filter_zero modality) in
          let (Cod (cfilter, cod)) = CodCube.find_top cods in
          let Eq = Modality.filter_uniq cfilter (Modality.filter_zero modality) in
          let (Wrap n) = pi_arity cod in
          Wrap (Suc n))
  | _ -> Wrap Zero

(* Collect the binder names of the zero-dimensional pi-types on the front of a term, in order, as a plain list — the names of the argument telescope of the constructor whose function-type this is, without reconstructing the telescope.  Used to name the pattern variables when displaying a "split". *)
let rec pi_names : type mode a. (mode, a, kinetic) term -> string option list = function
  | Pi { x; filter; doms = Modal (modality, _, _); cods } -> (
      match D.compare_zero (CodCube.dim cods) with
      | Pos _ -> []
      | Zero ->
          let Eq = Modality.filter_uniq filter (Modality.filter_zero modality) in
          let (Cod (cfilter, cod)) = CodCube.find_top cods in
          let Eq = Modality.filter_uniq cfilter (Modality.filter_zero modality) in
          option_of_binder_name (top_variable x) :: pi_names cod)
  | _ -> []

let rec dim_term_env : type mode a n b. (mode, a, n, b) env -> n D.t = function
  | Emp (_, n) -> n
  | Ext { env; _ } -> dim_term_env env
  | Key { env; _ } -> dim_term_env env
  | Prekey { env; _ } -> dim_term_env env

let dim_entry : type dom modality mode b f n bm. (dom, modality, mode, b, bm, f, n) entry -> n D.t =
  function
  | Vis { bindings; _ } -> CubeOf.dim bindings
  | Invis { bindings; _ } -> CubeOf.dim bindings

let plus_lock_entry : type dom modality mode b f n bm.
    (dom, modality, mode, b, bm, f, n) entry ->
    ((b, (modality, n) dim_entry) snoc, mode, modality, dom, bm) plus_lock = function
  | Vis { plus_lock; _ } -> plus_lock
  | Invis { plus_lock; _ } -> plus_lock

let modality_entry : type dom modality mode b f n bm.
    (dom, modality, mode, b, bm, f, n) entry -> (dom, modality, mode) Modality.t =
 fun e -> plus_lock_modality (plus_lock_entry e)

let filter_entry : type dom modality mode b f n bm.
    (dom, modality, mode, b, bm, f, n) entry -> (dom, modality, mode, n, n) Modality.filter_dim =
  function
  | Vis { filter; _ } -> filter
  | Invis { filter; _ } -> filter

module Termctx = struct
  type ('mode, 'a, 'b) ordered = ('mode, 'a, 'b) ordered_termctx
  type ('mode, 'a, 'b) t = ('mode, 'a, 'b) termctx

  let rec ordered_tctx : type mode a b. (mode, a, b) ordered_termctx -> (mode, b) Tctx.t = function
    | Emp mode -> Path (Suc (Zero, Proj mode), Unit)
    | Ext (ctx, e, _) -> Tctx.suc (ordered_tctx ctx) (Dim (dim_entry e, filter_entry e))
    | Lock (ctx, modality) -> Tctx.suc (ordered_tctx ctx) (Lock modality)
    | Weaken (ctx, _) -> ordered_tctx ctx

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
            filter = Modality.filter_zero (plus_lock_modality plus_lock);
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
    | Weaken (ctx, _) -> ordered_mode ctx

  let mode (Permute (_, ctx)) = ordered_mode ctx

  (* Remove *all* locks at the end of a context. *)

  type (_, _, _) ordered_remove_locks =
    | Ordered_remove_locks :
        ('cod, 'a, 'b) ordered * ('b, 'cod, 'modality, 'mode, 'bc) plus_lock * 'b ends_without_lock
        -> ('mode, 'a, 'bc) ordered_remove_locks

  let rec ordered_remove_locks : type mode a bc.
      (mode, a, bc) ordered -> (mode, a, bc) ordered_remove_locks =
   fun ctx ->
    match ctx with
    | Emp _ -> Ordered_remove_locks (ctx, plus_no_lock (ordered_mode ctx), Without_lock_proj)
    | Ext (_, _, _) -> Ordered_remove_locks (ctx, plus_no_lock (ordered_mode ctx), Without_lock_dim)
    | Weaken (ctx, code) ->
        let (Ordered_remove_locks (ctx, plus, wl)) = ordered_remove_locks ctx in
        Ordered_remove_locks (Weaken (ctx, code), plus, wl)
    | Lock (ctx, g) ->
        let (Ordered_remove_locks (ctx, plus, wl)) = ordered_remove_locks ctx in
        Ordered_remove_locks (ctx, plus_lock_suc plus g, wl)

  type (_, _) remove_locks =
    | Remove_locks :
        ('cod, 'a, 'b) t * ('b, 'cod, 'modality, 'mode, 'bc) plus_lock
        -> ('mode, 'bc) remove_locks

  let remove_locks : type mode a bc. (mode, a, bc) t -> (mode, bc) remove_locks =
   fun (Permute (p, ctx)) ->
    let (Ordered_remove_locks (ctx, plus, _)) = ordered_remove_locks ctx in
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
  | Weaken (ctx, _) ->
      (* The dataless weakening variable has no display name of its own; strip it and give it an anonymous hint. *)
      let (Snoc (vars, x)) = vars in
      Snoc (ordered_hole_vars ctx vars, binder_name_of_option x)
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
