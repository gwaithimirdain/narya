open Util
open Tbwd
open Dim
open Core
open Term

type 'n t

val empty : emp t
val remove : 'b t -> ('a, 'n, 'b) Tbwd.insert -> 'a t
val lookup : 'n t -> 'n index -> string list
val lookup_field : 'n t -> 'n index -> string -> string list option

val add_cube :
  ?force_names:bool -> 'n D.t -> 'b t -> string option -> string option * ('b, 'n) snoc t

val add : ?force_names:bool -> 'b t -> 'n variables -> 'n variables * ('b, 'n) snoc t
val add_full : 'b t -> 'mn variables -> 'mn variables * ('b, 'mn) snoc t
val of_ctx : ('a, 'b) Ctx.t -> 'b t

val uniquify_vars :
  (string option, 'a) Bwv.t -> (string * [ `Original | `Renamed ], 'a) Bwv.t * emp t

val unsafe_add : 'b t -> 'n variables -> (string, string) Abwd.t -> ('b, 'n) snoc t

type named_term = Named : 'a t * ('a, kinetic) term -> named_term
