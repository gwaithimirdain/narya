open Bwd
open Util
open Modal
open Tbwd
open Term
open Origin

type 'mode definition_args = {
  mode : 'mode Mode.t;
  ty : ('mode, emp, kinetic) term;
  tm : [ `Axiom | `Defined of ('mode, emp, potential) term ];
  parametric : [ `Parametric | `Nonparametric | `Maybe_parametric ];
}

type definition = Definition : 'mode definition_args -> definition

val find : Constant.t -> definition
val find_meta : ('mode, 'a, 'b, 's) Meta.t -> ('mode, 'a, 'b, 's) Metadef.t

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
  ('mode, emp, potential) term ->
  unit

val add_error : Constant.t -> Reporter.Code.t -> unit

val add_meta :
  ('mode, 'a, 'b, 's) Meta.t ->
  termctx:('mode, 'a, 'b) termctx ->
  ty:('mode, 'b, kinetic) term ->
  tm:[ `Defined of ('mode, 'b, 's) term | `Axiom ] ->
  energy:'s energy ->
  unit

val set_meta :
  ('mode, 'a, 'b, 's) Meta.t -> ?termctx:('mode, 'a, 'b) termctx -> ('mode, 'b, 's) term -> unit

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
  [ `Axiom | `Defined of ('mode, emp, potential) term ] ->
  (unit -> 'a) ->
  'a

val with_meta_definition : ('mode, 'a, 'b, 's) Meta.t -> ('mode, 'b, 's) term -> (unit -> 'x) -> 'x
val without_definition : Constant.t -> Reporter.Code.t -> (unit -> 'a) -> 'a
val without_meta_definition : ('mode, 'a, 'b, 's) Meta.t -> Reporter.Code.t -> (unit -> 'x) -> 'x
val set_nonparametric : Constant.t option -> unit
val set_parametric : Constant.t -> unit
val set_maybe_parametric : unit -> unit
val get_parametric : unit -> [ `Parametric | `Nonparametric ]
