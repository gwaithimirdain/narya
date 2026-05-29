open Modal
module Testmode = Mode.Generate (Trivial.TestmodeGen)

type test_mode = Testmode.t

module Testcell = Trivial.Idcell (Testmode)

let () = Modalcell.set_theory (module Testcell : Modalcell.Theory)
let test_mode = Testmode.mode
