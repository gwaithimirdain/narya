open Util

let install () = Io.unmarshal (Istream.string [%blob "hott.nyb"])
