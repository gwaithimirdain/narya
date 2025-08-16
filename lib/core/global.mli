open Bwd
open Util
open Tbwd
open Term
open Origin

type definition =
  [ `Axiom | `Defined of (emp, potential) term ]
  * [ `Parametric | `Nonparametric | `Maybe_parametric ]

val find : Constant.t -> (emp, kinetic) term * definition
val find_meta : ('a, 'b, 's) Meta.t -> ('a, 'b, 's) Metadef.t

type find_hole =
  | Found_hole : {
      meta : ('a, 'b, 's) Meta.t;
      instant : Instant.t;
      termctx : ('a, 'b) termctx;
      ty : ('b, kinetic) term;
      status : ('b, 's) Status.status;
      vars : (string option, 'a) Bwv.t;
      li : No.interval;
      ri : No.interval;
      parametric : [ `Parametric | `Nonparametric ];
    }
      -> find_hole

val find_hole : int -> find_hole
val all_holes : unit -> find_hole Bwd.t
val to_channel_file : Out_channel.t -> File.t -> Marshal.extern_flags list -> unit

type file_entry

val find_file : File.t -> file_entry
val add_file : File.t -> file_entry -> unit
val from_channel_file : (File.t -> File.t) -> In_channel.t -> File.t -> file_entry
val add : Constant.t -> (emp, kinetic) term -> definition -> unit
val set : Constant.t -> definition -> unit
val add_error : Constant.t -> Reporter.Code.t -> unit

val add_meta :
  ('a, 'b, 's) Meta.t ->
  termctx:('a, 'b) termctx ->
  ty:('b, kinetic) term ->
  tm:[ `Defined of ('b, 's) term | `Axiom ] ->
  energy:'s energy ->
  unit

val set_meta : ('a, 'b, 's) Meta.t -> tm:('b, 's) term -> unit
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
  ('a, 'b, 's) Meta.t ->
  Asai.Range.t ->
  vars:(string option, 'a) Bwv.t ->
  termctx:('a, 'b) termctx ->
  ty:('b, kinetic) term ->
  status:('b, 's) Status.status ->
  li:No.interval ->
  ri:No.interval ->
  unit

val with_definition :
  Constant.t -> [ `Axiom | `Defined of (emp, potential) term ] -> (unit -> 'a) -> 'a

val with_meta_definition : ('a, 'b, 's) Meta.t -> ('b, 's) term -> (unit -> 'x) -> 'x
val without_definition : Constant.t -> Reporter.Code.t -> (unit -> 'a) -> 'a
val without_meta_definition : ('a, 'b, 's) Meta.t -> Reporter.Code.t -> (unit -> 'x) -> 'x
val set_nonparametric : Constant.t option -> unit
val set_parametric : Constant.t -> unit
val set_maybe_parametric : unit -> unit
val get_parametric : unit -> [ `Parametric | `Nonparametric ]
