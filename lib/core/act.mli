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
  ('mode, 's) value -> ('m, 'n) deg -> ('mode, 'mu1, 'mu2, 'cod) Modalcell.t -> ('dom, 's) value

val act_normal :
  'mode normal -> ('a, 'b) deg -> ('mode, 'mu1, 'mu2, 'cod) Modalcell.t -> 'dom normal

val gact_ty :
  ?err:dim_err ->
  ('mode, kinetic) value option ->
  ('mode, kinetic) value ->
  ('a, 'b) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('dom, kinetic) value

val act_ty :
  ?err:dim_err ->
  ('mode, kinetic) value ->
  ('mode, kinetic) value ->
  ('a, 'b) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('dom, kinetic) value

val act_evaluation :
  ('mode, 's) evaluation ->
  ('m, 'n) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('dom, 's) evaluation

val act_value_cube :
  ('a -> ('mode, 's) value) ->
  ('n, 'a) CubeOf.t ->
  ('m, 'n) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('m, ('dom, 's) value) CubeOf.t

val act_lazy_eval :
  ('mode, 's) lazy_eval ->
  ('m, 'n) deg ->
  ('mode, 'mu1, 'mu2, 'cod) Modalcell.t ->
  ('dom, 's) lazy_eval

val field_lazy :
  ('mode, 's) lazy_eval -> 'i Field.t -> ('n, 't, 'i) insertion -> ('mode, 's) lazy_eval
