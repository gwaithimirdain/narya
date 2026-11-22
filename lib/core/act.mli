open Dim
open Modal
open Reporter
open Value

type ('mode, 'cod, 'a, 'b) actor = {
  act : 'm 'n 'mu1 'mu2. 'a -> ('m, 'n) deg -> ('mode, 'mu1, 'mu2, 'cod) Modalcell.t -> 'b;
}

val act_cube :
  ('mode, 'cod, 'a, 'b) actor ->
  ('n, 'a) CubeOf.t ->
  ('m, 'n) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('m, 'b) CubeOf.t

val act_value :
  ('mode, 's) value -> ('m, 'n) deg -> ('mode, 'mu1, 'mu2, 'cod) Modalcell.t -> ('mode, 's) value

val act_normal :
  'mode normal -> ('a, 'b) deg -> ('mode, 'mu1, 'mu2, 'cod) Modalcell.t -> 'mode normal

val gact_ty :
  ?err:dim_err ->
  ('mode, kinetic) value option ->
  ('mode, kinetic) value ->
  ('a, 'b) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('mode, kinetic) value

val act_ty :
  ?err:dim_err ->
  ('mode, kinetic) value ->
  ('mode, kinetic) value ->
  ('a, 'b) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('mode, kinetic) value

val act_evaluation :
  ('mode, 's) evaluation ->
  ('m, 'n) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('mode, 's) evaluation

val act_value_cube :
  ('a -> ('mode, 's) value) ->
  ('n, 'a) CubeOf.t ->
  ('m, 'n) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('m, ('mode, 's) value) CubeOf.t

val act_lazy_eval :
  ('mode, 's) lazy_eval ->
  ('m, 'n) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('mode, 's) lazy_eval

val field_lazy :
  ('src, 'f, 'mode) Modality.t ->
  ('src, 's) lazy_eval ->
  'i Field.t ->
  ('n, 't, 'i) insertion ->
  ('mode, 's) lazy_eval

type _ pushed_stuck =
  | Pushed_stuck : ('hmode, potential) head * ('hmode, 'mode, 'any, live) apps -> 'mode pushed_stuck

val push_stuck : 'mode stuck -> 'mode pushed_stuck

type (_, _) stuck_split_inst =
  | No_inst : ('hmode, 'mode, noninst) stuck_spine -> ('hmode, 'mode) stuck_split_inst
  | Has_inst :
      ('hmode, 'mode, noninst) stuck_spine * 'k D.pos * ('n, 'k, 'nk, 'mode normal) TubeOf.t
      -> ('hmode, 'mode) stuck_split_inst

val stuck_split_inst : ('hmode, 'mode, 'any) stuck_spine -> ('hmode, 'mode) stuck_split_inst
