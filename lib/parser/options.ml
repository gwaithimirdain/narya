(* Configuration options that affect the following code, and are scoped in sections, but don't change the underlying type theory. *)

type implicitness = [ `Implicit | `Explicit ]
type values = |

let to_string : values -> string = function
  | _ -> .

type t = unit

let default : t = ()
