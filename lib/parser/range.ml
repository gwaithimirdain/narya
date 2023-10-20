open Fmlib_parse
open Asai.Span
open Core.Reporter

module S = Algaeff.Reader.Make (struct
  type env = string
end)

let convert_pos (src : source) pos inc =
  let start_of_line = Position.byte_offset_bol pos in
  (* It appears that fmlib lines are 0-indexed and Asai lines are 1-indexed *)
  let line_num = Position.line pos + 1 in
  let offset = Position.byte_offset pos + inc in
  { source = src; offset; start_of_line; line_num }

let convert (pos1, pos2) =
  (* In case of a lexing or parsing error at end of input, Fmlib returns a 0-width range.  Asai doesn't know how to deal with that, so we extend the string a bit to mark the error as occurring at EOF. *)
  let str = S.read () in
  let str, inc =
    if pos1 = pos2 then
      if Position.byte_offset pos2 = String.length str then (str ^ "<EOF>", 5)
        (* Fmlib also reports a 0-width range in mid-parse if we fail directly (i.e. with "fail" or "unexpected" rather than during a lookahead such as "step").  But our calls to "fail" all include an explicit range, and we never call "unexpected".  Thus I don't think this should happen, so we flag it as an Anomaly.  *)
      else fatal (Anomaly "Zero-width range during parse failure before EOF")
    else (str, 0) in
  let source = `String { title = Some "user-supplied term"; content = str } in
  make (convert_pos source pos1 0, convert_pos source pos2 inc)

let run = S.run
