open Util
open Tbwd
open Dim
open Core
open Tctx
open Term

type 'n t
type wrapped = Wrap : 'n t -> wrapped

val empty : 'mode emp t
val remove : 'b t -> ('a, 'modality, 'n, 'b) insert -> 'a t
val split : 'ab t -> ('x, 'b, 'y, 'a, 'z, 'ab) Tctx.comp -> 'a t
val lookup : 'n t -> ('mode, 'n) index -> string list
val lookup_field : 'n t -> ('mode, 'n) index -> string -> string list option
val add_cube : 'n D.t -> 'b t -> binder_name -> string * ('b, ('m, 'n) dim_entry) snoc t

val add_fields :
  'n D.t -> 'b t -> string list -> (('b, ('m, 'n) dim_entry) snoc t * string list) option

val add : 'b t -> 'n variables -> ('n, string) gvariables * ('b, ('m, 'n) dim_entry) snoc t

val add_strings :
  'b t -> ('n, string) gvariables -> ('n, string) gvariables * ('b, ('m, 'n) dim_entry) snoc t

val add_full :
  'b t -> 'mn variables -> ('mn, string) gvariables * ('b, ('modality, 'mn) dim_entry) snoc t

val add_lock : 'a t -> ('a, 'mode, 'modality, 'dom, 'am) plus_lock -> 'am t
val of_ctx : ('mode, 'a, 'b) Ctx.t -> 'b t
val degenerate : 'r D.t -> ('r, 'b, 'kb, 'mode) plusmap -> 'b t -> 'kb t

type uniquified_vars

val of_uniquified_vars : uniquified_vars -> 'mode emp t

val uniquify_vars :
  (binder_name, 'a) Bwv.t -> (string * [ `Original | `Renamed ], 'a) Bwv.t * uniquified_vars

val unsafe_add :
  'b t ->
  ('n, string) gvariables ->
  (string, string) Abwd.t ->
  ('b, ('modality, 'n) dim_entry) snoc t

type _ named_term = Named : 'a t * ('mode, 'a, kinetic) term -> 'mode named_term
