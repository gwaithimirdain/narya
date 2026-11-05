open Bwd

let split_utf8_bwd s =
  let len = String.length s in
  let rec loop i acc =
    if i >= len then acc
    else
      let decode = String.get_utf_8_uchar s i in
      let clen = Uchar.utf_decode_length decode in
      let char_str = String.sub s i clen in
      loop (i + clen) (Snoc (acc, char_str)) in
  loop 0 Emp

let split_utf8 s = Bwd.to_list (split_utf8_bwd s)

(* A string of n primes, using the multiple-prime characters where possible. *)
let rec primes n =
  if n <= 0 then ""
  else if n = 1 then "′"
  else if n = 2 then "″"
  else if n = 3 then "‴"
  else "⁗" ^ primes (n - 4)
