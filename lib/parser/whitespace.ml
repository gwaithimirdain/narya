type t = [ `Block of string | `Line of string | `Newlines of int ]
type alist = (Token.t * t list) list

let ensure_starting_newlines (k : int) (ws : t list) : t list =
  match ws with
  | `Newlines n :: _ when n >= k -> ws
  | _ -> `Newlines k :: ws

let rec ensure_ending_newlines (k : int) (ws : t list) : t list =
  match ws with
  | [] -> [ `Newlines k ]
  | [ `Newlines n ] -> [ `Newlines (max n k) ]
  | w :: ws -> w :: ensure_ending_newlines k ws
