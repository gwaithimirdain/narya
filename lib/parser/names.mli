open Util
open Tbwd
open Dim
open Core
open Term

type 'n t
type wrapped = Wrap : 'n t -> wrapped

val empty : emp t
val remove : 'b t -> ('a, 'n, 'b) Tbwd.insert -> 'a t
val permute : ('c, 'b) Tbwd.permute -> 'b t -> 'c t
val lookup : 'n t -> 'n index -> string list
val lookup_field : 'n t -> 'n index -> string -> string list option
val add_cube : 'n D.t -> 'b t -> binder_name -> string * ('b, 'n) snoc t
val add_fields : 'n D.t -> 'b t -> string list -> (('b, 'n) snoc t * string list) option
val add : 'b t -> 'n variables -> ('n, string) gvariables * ('b, 'n) snoc t
val add_strings : 'b t -> ('n, string) gvariables -> ('n, string) gvariables * ('b, 'n) snoc t
val add_full : 'b t -> 'mn variables -> ('mn, string) gvariables * ('b, 'mn) snoc t
val of_ctx : ('a, 'b) Ctx.t -> 'b t
val degenerate : 'r D.t -> ('r, 'b, 'kb) Plusmap.t -> 'b t -> 'kb t
val uniquify_vars : (binder_name, 'a) Bwv.t -> (string * [ `Original | `Renamed ], 'a) Bwv.t * emp t
val unsafe_add : 'b t -> ('n, string) gvariables -> (string, string) Abwd.t -> ('b, 'n) snoc t

type named_term = Named : 'a t * ('a, kinetic) term -> named_term
