open Dim
open Reporter
open Value

type ('a, 'b) actor = { act : 'm 'n. 'a -> ('m, 'n) deg -> 'b }

val act_cube : ('a, 'b) actor -> ('n, 'a) CubeOf.t -> ('m, 'n) deg -> ('m, 'b) CubeOf.t
val act_value : ('mode, 's) value -> ('m, 'n) deg -> ('mode, 's) value
val act_normal : 'mode normal -> ('a, 'b) deg -> 'mode normal
val gact_ty : ?err:dim_err -> ('mode, kinetic) value option -> ('mode, kinetic) value -> ('a, 'b) deg -> ('mode, kinetic) value
val act_ty : ?err:dim_err -> ('mode, kinetic) value -> ('mode, kinetic) value -> ('a, 'b) deg -> ('mode, kinetic) value
val act_evaluation : ('mode, 's) evaluation -> ('m, 'n) deg -> ('mode, 's) evaluation

val act_value_cube :
  ('a -> ('mode, 's) value) -> ('n, 'a) CubeOf.t -> ('m, 'n) deg -> ('m, ('mode, 's) value) CubeOf.t

val act_lazy_eval : ('mode, 's) lazy_eval -> ('m, 'n) deg -> ('mode, 's) lazy_eval
val field_lazy : ('mode, 's) lazy_eval -> 'i Field.t -> ('n, 't, 'i) insertion -> ('mode, 's) lazy_eval
