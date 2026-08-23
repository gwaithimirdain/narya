open Util
open Tbwd
open Dim
open Core
open Tctx
open Term

(* A collection of variable names for a context, parametrized by the type of the alternative payload that an entry may carry in place of a name (see the comment in names.ml).  A client with no use for such entries instantiates it arbitrarily. *)
type ('x, 'n) t
type 'x wrapped = Wrap : ('x, 'n) t -> 'x wrapped

val empty : ('x, 'mode emp) t
val remove : ('x, 'b) t -> ('a, 'modality, 'n, 'b) insert -> ('x, 'a) t
val split : ('x, 'ab) t -> ('p, 'b, 'q, 'a, 'r, 'ab) Tctx.comp -> ('x, 'a) t
val permute : ('a, 'b) permute -> ('x, 'b) t -> ('x, 'a) t

val add_match_vars :
  ('x, 'a) t ->
  ('n, 'mode, 'annotations, 'mode, 'mode, 'b, 'mode) VarAnnotate.fwd_t ->
  ('mode, 'b, 'mode, 'a, unit, 'ab) Tctx.bcomp ->
  ('x, 'ab) t * string list

val lookup : ('x, 'n) t -> ('mode, 'n) index -> [ `Name of string list | `Other of 'x ]
val lookup_field : ('x, 'n) t -> ('mode, 'n) index -> string -> string list option
val add_cube : 'n D.t -> ('x, 'b) t -> binder_name -> string * ('x, ('b, ('m, 'n) dim_entry) snoc) t
val add_other : ('x, 'b) t -> 'x -> ('x, ('b, ('m, 'n) dim_entry) snoc) t

val add_fields :
  'n D.t ->
  ('x, 'b) t ->
  string list ->
  (('x, ('b, ('m, 'n) dim_entry) snoc) t * string list) option

val add :
  ('x, 'b) t -> 'n variables -> ('n, string) gvariables * ('x, ('b, ('m, 'n) dim_entry) snoc) t

val add_strings :
  ('x, 'b) t ->
  ('n, string) gvariables ->
  ('n, string) gvariables * ('x, ('b, ('m, 'n) dim_entry) snoc) t

val add_full :
  ('x, 'b) t ->
  'mn variables ->
  ('mn, string) gvariables * ('x, ('b, ('modality, 'mn) dim_entry) snoc) t

val add_lock : ('x, 'a) t -> ('a, 'mode, 'modality, 'dom, 'am) plus_lock -> ('x, 'am) t
val of_ctx : ('mode, 'a, 'b) Ctx.t -> ('x, 'b) t
val degenerate : 'r D.t -> ('r, 'b, 'kb, 'mode) plusmap -> ('x, 'b) t -> ('x, 'kb) t

type uniquified_vars

val of_uniquified_vars : uniquified_vars -> ('x, 'mode emp) t

val uniquify_vars :
  (binder_name, 'a) Bwv.t -> (string * [ `Original | `Renamed ], 'a) Bwv.t * uniquified_vars

val unsafe_add :
  ('x, 'b) t ->
  ('n, string) gvariables ->
  (string, string) Abwd.t ->
  ('x, ('b, ('modality, 'n) dim_entry) snoc) t

type (_, _) named_term = Named : ('x, 'a) t * ('mode, 'a, kinetic) term -> ('x, 'mode) named_term
