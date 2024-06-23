open Util
open Tbwd
open Syntax
open Term

type definition = Axiom of [ `Parametric | `Nonparametric ] | Defined of (emp, potential) term

val find : Constant.t -> (emp, kinetic) term * definition
val find_meta : ('b, 's) Meta.t -> (unit, 'b * 's) Eternity.metadef
val to_channel_unit : Out_channel.t -> Compunit.t -> Marshal.extern_flags list -> unit
val from_channel_unit : (Compunit.t -> Compunit.t) -> In_channel.t -> Compunit.t -> unit
val locked : unit -> bool
val run_empty : (unit -> 'a) -> 'a
val add : Constant.t -> (emp, kinetic) term -> definition -> unit
val add_error : Constant.t -> Reporter.Code.t -> unit
val add_meta : ('b, 's) Meta.t -> (unit, 'b * 's) Eternity.metadef -> unit
val run_with : Constant.t -> (emp, kinetic) term -> definition -> (unit -> 'a) -> 'a
val run_with_definition : Constant.t -> definition -> (unit -> 'a) -> 'a
val run_with_meta_definition : ('b, 's) Meta.t -> ('b, 's) Eternity.meta_value -> (unit -> 'a) -> 'a
val run_locked : (unit -> 'a) -> 'a
