open Bwd
open Util
open Modal
open Tctx
open Term
open Origin

type 'mode definition_args = {
  mode : 'mode Mode.t;
  ty : ('mode, 'mode emp, kinetic) term;
  tm : [ `Axiom | `Defined of ('mode, 'mode emp, potential) term ];
  parametric : [ `Parametric | `Nonparametric | `Maybe_parametric ];
}

type definition = Definition : 'mode definition_args -> definition

val register_invalidator : (unit -> unit) -> unit
val find_const : Constant.t -> definition
val find_meta : ('mode, 'a, 'b, 's) Meta.t -> ('mode, 'a, 'b, 's) Metadef.t
val meta_name : ?owner_name:(Constant.t -> string) -> ('mode, 'a, 'b, 's) Meta.t -> string
val with_owner_of : ('mode, 'a, 'b, 's) Meta.t -> (unit -> 'x) -> 'x

type find_hole =
  | Found_hole : {
      meta : ('mode, 'a, 'b, 's) Meta.t;
      instant : Instant.t;
      termctx : ('mode, 'a, 'b) termctx;
      ty : ('mode, 'b, kinetic) term;
      status : ('mode, 'b, 's) Status.status;
      vars : (string option, 'a) Bwv.t;
      li : No.interval;
      ri : No.interval;
      parametric : [ `Parametric | `Nonparametric ];
      beingdefined : unit Constant.Map.t;
    }
      -> find_hole

val find_hole : int -> find_hole
val all_holes : unit -> find_hole Bwd.t
val to_channel_origin : Out_channel.t -> Origin.t -> Marshal.extern_flags list -> unit

type origin_entry

val find_file : File.t -> origin_entry
val add_file : File.t -> origin_entry -> unit
val from_istream_origin : (File.t -> File.t) -> Istream.t -> Origin.t -> origin_entry
val add : Constant.t -> definition -> unit

val set :
  Constant.t ->
  'mode Mode.t ->
  ?parametric:[ `Parametric | `Maybe_parametric | `Nonparametric ] ->
  ('mode, 'mode emp, potential) term ->
  unit

val add_error : Constant.t -> Reporter.Code.t -> unit

val add_meta :
  ?local:string ->
  ('mode, 'a, 'b, 's) Meta.t ->
  termctx:('mode, 'a, 'b) termctx ->
  ty:('mode, 'b, kinetic) term ->
  tm:[ `Defined of ('mode, 'b, 's) term | `Axiom ] ->
  energy:'s energy ->
  unit

val add_meta_error : ('mode, 'a, 'b, 's) Meta.t -> Reporter.Code.t -> unit

val set_meta :
  ('mode, 'a, 'b, 's) Meta.t ->
  ?termctx:('mode, 'a, 'b) termctx ->
  ?recursion:Positivity.recursion ->
  ('mode, 'b, 's) term ->
  unit

val add_unif :
  ('mode, 'a, 'b, kinetic) Meta.t ->
  ('mode, 'b, kinetic) term option ref ->
  ctx:('mode, 'a, 'b) Ctx.t ->
  ty:('mode, 'b, kinetic) term ->
  termctx:('mode, 'a, 'b) termctx Lazy.t ->
  unit

val unif_ctx : ('mode, 'a, 'b, kinetic) Meta.t -> ('mode, 'a, 'b) Ctx.t
val unif_assignable : ('mode, 'a, 'b, kinetic) Meta.t -> bool
val solve_unif : ('mode, 'a, 'b, kinetic) Meta.t -> ('mode, 'b, kinetic) term -> unit

val unif_solution :
  ('mode, 'a, 'b, kinetic) Meta.t ->
  ('mode, 'b, kinetic) term option ref ->
  ('mode, 'b, kinetic) term option

val unsolved_unifs : unit -> bool

val unif_solution_opt :
  ('mode, 'a, 'b, kinetic) Meta.t ->
  ('mode, 'b, kinetic) term option ref ->
  ('mode, 'b, kinetic) term option

val unif_status :
  ('mode, 'a, 'b, kinetic) Meta.t ->
  ('mode, 'b, kinetic) term option ref ->
  [ `Unsolved | `Speculative | `Written ]

val meta_termctx :
  ('mode, 'a, 'b, 's) Meta.t -> ('mode, 'b, 's, 'e) meta_kind -> ('mode, 'a, 'b) termctx

val meta_ty :
  ('mode, 'a, 'b, 's) Meta.t -> ('mode, 'b, 's, 'e) meta_kind -> ('mode, 'b, kinetic) term

val unsolved_holes : unit -> int
val current_unsolved_holes : unit -> int
val notify_holes : unit -> unit

(* *)
val run_command :
  holes_allowed:(unit, string) Result.t ->
  (unit -> int option * (int -> Reporter.Code.t option)) ->
  int option * (int * int * int) list

val run_command_then_undo :
  holes_allowed:(unit, string) Result.t ->
  (unit -> int option * (int -> Reporter.Code.t option)) ->
  int option * (int * int * int) list

val rewind_command :
  parametric:[ `Parametric | `Nonparametric ] ->
  holes_allowed:(unit, string) Result.t ->
  Instant.t ->
  (unit -> int option * (int -> Reporter.Code.t option)) ->
  int option * (int * int * int) list

val rewind_command_then_undo :
  parametric:[ `Parametric | `Nonparametric ] ->
  holes_allowed:(unit, string) Result.t ->
  Instant.t ->
  (unit -> int option * (int -> Reporter.Code.t option)) ->
  int option * (int * int * int) list

val run : (unit -> 'a) -> 'a

val add_hole :
  ('mode, 'a, 'b, 's) Meta.t ->
  Asai.Range.t ->
  vars:(string option, 'a) Bwv.t ->
  termctx:('mode, 'a, 'b) termctx ->
  ty:('mode, 'b, kinetic) term ->
  status:('mode, 'b, 's) Status.status ->
  li:No.interval ->
  ri:No.interval ->
  unit

val with_definition :
  Constant.t ->
  'mode Mode.t ->
  [ `Axiom | `Defined of ('mode, 'mode emp, potential) term ] ->
  (unit -> 'a) ->
  'a

val with_meta_definition : ('mode, 'a, 'b, 's) Meta.t -> ('mode, 'b, 's) term -> (unit -> 'x) -> 'x
val set_nonparametric : Constant.t option -> unit
val set_parametric : Constant.t -> unit
val set_maybe_parametric : unit -> unit
val get_parametric : unit -> [ `Parametric | `Nonparametric ]
