open Testutil.Pmp

let uu, _ = synth UU
let xx = assume "X" uu

(* Bottom face *)

let x000 = assume "x000" xx
let x001 = assume "x001" xx
let xx002, _ = synth (id !!"X" !!"x000" !!"x001")
let x002 = assume "x002" xx002
let x010 = assume "x010" xx
let x011 = assume "x011" xx
let xx012, _ = synth (id !!"X" !!"x010" !!"x011")
let x012 = assume "x012" xx012
let xx020, _ = synth (id !!"X" !!"x000" !!"x010")
let xx021, _ = synth (id !!"X" !!"x001" !!"x011")
let x020 = assume "x020" xx020
let x021 = assume "x021" xx021

let xx022, _ =
  synth
    (refl (refl !!"X")
    $ !!"x000"
    $ !!"x001"
    $ !!"x002"
    $ !!"x010"
    $ !!"x011"
    $ !!"x012"
    $ !!"x020"
    $ !!"x021")

let x022 = assume "x022" xx022

(* Top face *)

let x100 = assume "x100" xx
let x101 = assume "x101" xx
let xx102, _ = synth (id !!"X" !!"x100" !!"x101")
let x102 = assume "x102" xx102
let x110 = assume "x110" xx
let x111 = assume "x111" xx
let xx112, _ = synth (id !!"X" !!"x110" !!"x111")
let x112 = assume "x112" xx112
let xx120, _ = synth (id !!"X" !!"x100" !!"x110")
let xx121, _ = synth (id !!"X" !!"x101" !!"x111")
let x120 = assume "x120" xx120
let x121 = assume "x121" xx121

let xx122, _ =
  synth
    (refl (refl !!"X")
    $ !!"x100"
    $ !!"x101"
    $ !!"x102"
    $ !!"x110"
    $ !!"x111"
    $ !!"x112"
    $ !!"x120"
    $ !!"x121")

let x122 = assume "x122" xx122

(* Front face *)

let xx200, _ = synth (id !!"X" !!"x000" !!"x100")
let x200 = assume "x200" xx200
let xx201, _ = synth (id !!"X" !!"x001" !!"x101")
let x201 = assume "x201" xx201

let xx202, _ =
  synth
    (refl (refl !!"X")
    $ !!"x000"
    $ !!"x001"
    $ !!"x002"
    $ !!"x100"
    $ !!"x101"
    $ !!"x102"
    $ !!"x200"
    $ !!"x201")

let x202 = assume "x202" xx202

(* Back face *)

let xx210, _ = synth (id !!"X" !!"x010" !!"x110")
let x210 = assume "x210" xx210
let xx211, _ = synth (id !!"X" !!"x011" !!"x111")
let x211 = assume "x211" xx211

let xx212, _ =
  synth
    (refl (refl !!"X")
    $ !!"x010"
    $ !!"x011"
    $ !!"x012"
    $ !!"x110"
    $ !!"x111"
    $ !!"x112"
    $ !!"x210"
    $ !!"x211")

let x212 = assume "x212" xx212

(* Left face *)

let xx220, _ =
  synth
    (refl (refl !!"X")
    $ !!"x000"
    $ !!"x010"
    $ !!"x020"
    $ !!"x100"
    $ !!"x110"
    $ !!"x120"
    $ !!"x200"
    $ !!"x210")

let x220 = assume "x220" xx220

(* Right face *)

let xx221, _ =
  synth
    (refl (refl !!"X")
    $ !!"x001"
    $ !!"x011"
    $ !!"x021"
    $ !!"x101"
    $ !!"x111"
    $ !!"x121"
    $ !!"x201"
    $ !!"x211")

let x221 = assume "x221" xx221

(* Center *)

let xx222, _ =
  synth
    (refl (refl (refl !!"X"))
    $ !!"x000"
    $ !!"x001"
    $ !!"x002"
    $ !!"x010"
    $ !!"x011"
    $ !!"x012"
    $ !!"x020"
    $ !!"x021"
    $ !!"x022"
    $ !!"x100"
    $ !!"x101"
    $ !!"x102"
    $ !!"x110"
    $ !!"x111"
    $ !!"x112"
    $ !!"x120"
    $ !!"x121"
    $ !!"x122"
    $ !!"x200"
    $ !!"x201"
    $ !!"x202"
    $ !!"x210"
    $ !!"x211"
    $ !!"x212"
    $ !!"x220"
    $ !!"x221")

let x222 = assume "x222" xx222

(* The two transpositions that can act on a cube *)

let sym_x222, sym_xx222 = synth (sym !!"x222")

let apsym_x222, apsym_xx222 =
  synth
    (refl
       ("y00"
        @-> "y01"
        @-> "y02"
        @-> "y10"
        @-> "y11"
        @-> "y12"
        @-> "y20"
        @-> "y21"
        @-> "y22"
        @-> sym !!"y22"
       <:> ("y00", !!"X")
           @=> ("y01", !!"X")
           @=> ("y02", id !!"X" !!"y00" !!"y01")
           @=> ("y10", !!"X")
           @=> ("y11", !!"X")
           @=> ("y12", id !!"X" !!"y10" !!"y11")
           @=> ("y20", id !!"X" !!"y00" !!"y10")
           @=> ("y21", id !!"X" !!"y01" !!"y11")
           @=> ( "y22",
                 refl (refl !!"X")
                 $ !!"y00"
                 $ !!"y01"
                 $ !!"y02"
                 $ !!"y10"
                 $ !!"y11"
                 $ !!"y12"
                 $ !!"y20"
                 $ !!"y21" )
           @=> (refl (refl !!"X")
               $ !!"y00"
               $ !!"y10"
               $ !!"y20"
               $ !!"y01"
               $ !!"y11"
               $ !!"y21"
               $ !!"y02"
               $ !!"y12"))
    $ !!"x000"
    $ !!"x001"
    $ !!"x002"
    $ !!"x010"
    $ !!"x011"
    $ !!"x012"
    $ !!"x020"
    $ !!"x021"
    $ !!"x022"
    $ !!"x100"
    $ !!"x101"
    $ !!"x102"
    $ !!"x110"
    $ !!"x111"
    $ !!"x112"
    $ !!"x120"
    $ !!"x121"
    $ !!"x122"
    $ !!"x200"
    $ !!"x201"
    $ !!"x202"
    $ !!"x210"
    $ !!"x211"
    $ !!"x212"
    $ !!"x220"
    $ !!"x221"
    $ !!"x222")

(* They have different types *)
let () = unequal sym_xx222 apsym_xx222

(* Here are their types. *)
let sym_xx222', _ =
  synth
    (refl (refl (refl !!"X"))
    $ !!"x000"
    $ !!"x010"
    $ !!"x020"
    $ !!"x001"
    $ !!"x011"
    $ !!"x021"
    $ !!"x002"
    $ !!"x012"
    $ sym !!"x022"
    $ !!"x100"
    $ !!"x110"
    $ !!"x120"
    $ !!"x101"
    $ !!"x111"
    $ !!"x121"
    $ !!"x102"
    $ !!"x112"
    $ sym !!"x122"
    $ !!"x200"
    $ !!"x210"
    $ !!"x220"
    $ !!"x201"
    $ !!"x211"
    $ !!"x221"
    $ !!"x202"
    $ !!"x212")

let () = equal sym_xx222 sym_xx222'

let apsym_xx222', _ =
  synth
    (refl (refl (refl !!"X"))
    $ !!"x000"
    $ !!"x001"
    $ !!"x002"
    $ !!"x100"
    $ !!"x101"
    $ !!"x102"
    $ !!"x200"
    $ !!"x201"
    $ !!"x202"
    $ !!"x010"
    $ !!"x011"
    $ !!"x012"
    $ !!"x110"
    $ !!"x111"
    $ !!"x112"
    $ !!"x210"
    $ !!"x211"
    $ !!"x212"
    $ !!"x020"
    $ !!"x021"
    $ !!"x022"
    $ !!"x120"
    $ !!"x121"
    $ !!"x122"
    $ sym !!"x220"
    $ sym !!"x221")

let () = equal apsym_xx222 apsym_xx222'

(* They both have alternative degeneracy notations. *)

let sym_x222', sym_xx222' = synth (!!"x222" $^ "213")
let () = equal sym_xx222 sym_xx222'
let () = equal sym_x222 sym_x222'
let apsym_x222', apsym_xx222' = synth (!!"x222" $^ "132")
let () = equal apsym_xx222 apsym_xx222'
let () = equal apsym_x222 apsym_x222'

(* But the two sides of the braid equation are equal.  We build them up in stages, checking their types as we go.  First the left-hand side sym-apsym-sym. *)

let apsym_sym_x222, apsym_sym_xx222 =
  synth
    (refl
       ("y00"
        @-> "y01"
        @-> "y02"
        @-> "y10"
        @-> "y11"
        @-> "y12"
        @-> "y20"
        @-> "y21"
        @-> "y22"
        @-> sym !!"y22"
       <:> ("y00", !!"X")
           @=> ("y01", !!"X")
           @=> ("y02", id !!"X" !!"y00" !!"y01")
           @=> ("y10", !!"X")
           @=> ("y11", !!"X")
           @=> ("y12", id !!"X" !!"y10" !!"y11")
           @=> ("y20", id !!"X" !!"y00" !!"y10")
           @=> ("y21", id !!"X" !!"y01" !!"y11")
           @=> ( "y22",
                 refl (refl !!"X")
                 $ !!"y00"
                 $ !!"y01"
                 $ !!"y02"
                 $ !!"y10"
                 $ !!"y11"
                 $ !!"y12"
                 $ !!"y20"
                 $ !!"y21" )
           @=> (refl (refl !!"X")
               $ !!"y00"
               $ !!"y10"
               $ !!"y20"
               $ !!"y01"
               $ !!"y11"
               $ !!"y21"
               $ !!"y02"
               $ !!"y12"))
    $ !!"x000"
    $ !!"x010"
    $ !!"x020"
    $ !!"x001"
    $ !!"x011"
    $ !!"x021"
    $ !!"x002"
    $ !!"x012"
    $ sym !!"x022"
    $ !!"x100"
    $ !!"x110"
    $ !!"x120"
    $ !!"x101"
    $ !!"x111"
    $ !!"x121"
    $ !!"x102"
    $ !!"x112"
    $ sym !!"x122"
    $ !!"x200"
    $ !!"x210"
    $ !!"x220"
    $ !!"x201"
    $ !!"x211"
    $ !!"x221"
    $ !!"x202"
    $ !!"x212"
    $ sym !!"x222")

let apsym_sym_xx222', _ =
  synth
    (refl (refl (refl !!"X"))
    $ !!"x000"
    $ !!"x010"
    $ !!"x020"
    $ !!"x100"
    $ !!"x110"
    $ !!"x120"
    $ !!"x200"
    $ !!"x210"
    $ !!"x220"
    $ !!"x001"
    $ !!"x011"
    $ !!"x021"
    $ !!"x101"
    $ !!"x111"
    $ !!"x121"
    $ !!"x201"
    $ !!"x211"
    $ !!"x221"
    $ !!"x002"
    $ !!"x012"
    $ sym !!"x022"
    $ !!"x102"
    $ !!"x112"
    $ sym !!"x122"
    $ sym !!"x202"
    $ sym !!"x212")

let () = equal apsym_sym_xx222 apsym_sym_xx222'

let sym_apsym_sym_x222, sym_apsym_sym_xx222 =
  synth
    (sym
       (refl
          ("y00"
           @-> "y01"
           @-> "y02"
           @-> "y10"
           @-> "y11"
           @-> "y12"
           @-> "y20"
           @-> "y21"
           @-> "y22"
           @-> sym !!"y22"
          <:> ("y00", !!"X")
              @=> ("y01", !!"X")
              @=> ("y02", id !!"X" !!"y00" !!"y01")
              @=> ("y10", !!"X")
              @=> ("y11", !!"X")
              @=> ("y12", id !!"X" !!"y10" !!"y11")
              @=> ("y20", id !!"X" !!"y00" !!"y10")
              @=> ("y21", id !!"X" !!"y01" !!"y11")
              @=> ( "y22",
                    refl (refl !!"X")
                    $ !!"y00"
                    $ !!"y01"
                    $ !!"y02"
                    $ !!"y10"
                    $ !!"y11"
                    $ !!"y12"
                    $ !!"y20"
                    $ !!"y21" )
              @=> (refl (refl !!"X")
                  $ !!"y00"
                  $ !!"y10"
                  $ !!"y20"
                  $ !!"y01"
                  $ !!"y11"
                  $ !!"y21"
                  $ !!"y02"
                  $ !!"y12"))
       $ !!"x000"
       $ !!"x010"
       $ !!"x020"
       $ !!"x001"
       $ !!"x011"
       $ !!"x021"
       $ !!"x002"
       $ !!"x012"
       $ sym !!"x022"
       $ !!"x100"
       $ !!"x110"
       $ !!"x120"
       $ !!"x101"
       $ !!"x111"
       $ !!"x121"
       $ !!"x102"
       $ !!"x112"
       $ sym !!"x122"
       $ !!"x200"
       $ !!"x210"
       $ !!"x220"
       $ !!"x201"
       $ !!"x211"
       $ !!"x221"
       $ !!"x202"
       $ !!"x212"
       $ sym !!"x222"))

let sym_apsym_sym_xx222', _ =
  synth
    (refl (refl (refl !!"X"))
    $ !!"x000"
    $ !!"x100"
    $ !!"x200"
    $ !!"x010"
    $ !!"x110"
    $ !!"x210"
    $ !!"x020"
    $ !!"x120"
    $ sym !!"x220"
    $ !!"x001"
    $ !!"x101"
    $ !!"x201"
    $ !!"x011"
    $ !!"x111"
    $ !!"x211"
    $ !!"x021"
    $ !!"x121"
    $ sym !!"x221"
    $ !!"x002"
    $ !!"x102"
    $ sym !!"x202"
    $ !!"x012"
    $ !!"x112"
    $ sym !!"x212"
    $ sym !!"x022"
    $ sym !!"x122")

let () = equal sym_apsym_sym_xx222 sym_apsym_sym_xx222'

(* Now the right-hand side, apsym-sym-apsym *)

let sym_apsym_x222, sym_apsym_xx222 =
  synth
    (sym
       (refl
          ("y00"
           @-> "y01"
           @-> "y02"
           @-> "y10"
           @-> "y11"
           @-> "y12"
           @-> "y20"
           @-> "y21"
           @-> "y22"
           @-> sym !!"y22"
          <:> ("y00", !!"X")
              @=> ("y01", !!"X")
              @=> ("y02", id !!"X" !!"y00" !!"y01")
              @=> ("y10", !!"X")
              @=> ("y11", !!"X")
              @=> ("y12", id !!"X" !!"y10" !!"y11")
              @=> ("y20", id !!"X" !!"y00" !!"y10")
              @=> ("y21", id !!"X" !!"y01" !!"y11")
              @=> ( "y22",
                    refl (refl !!"X")
                    $ !!"y00"
                    $ !!"y01"
                    $ !!"y02"
                    $ !!"y10"
                    $ !!"y11"
                    $ !!"y12"
                    $ !!"y20"
                    $ !!"y21" )
              @=> (refl (refl !!"X")
                  $ !!"y00"
                  $ !!"y10"
                  $ !!"y20"
                  $ !!"y01"
                  $ !!"y11"
                  $ !!"y21"
                  $ !!"y02"
                  $ !!"y12"))
       $ !!"x000"
       $ !!"x001"
       $ !!"x002"
       $ !!"x010"
       $ !!"x011"
       $ !!"x012"
       $ !!"x020"
       $ !!"x021"
       $ !!"x022"
       $ !!"x100"
       $ !!"x101"
       $ !!"x102"
       $ !!"x110"
       $ !!"x111"
       $ !!"x112"
       $ !!"x120"
       $ !!"x121"
       $ !!"x122"
       $ !!"x200"
       $ !!"x201"
       $ !!"x202"
       $ !!"x210"
       $ !!"x211"
       $ !!"x212"
       $ !!"x220"
       $ !!"x221"
       $ !!"x222"))

let sym_apsym_xx222', _ =
  synth
    (refl (refl (refl !!"X"))
    $ !!"x000"
    $ !!"x100"
    $ !!"x200"
    $ !!"x001"
    $ !!"x101"
    $ !!"x201"
    $ !!"x002"
    $ !!"x102"
    $ sym !!"x202"
    $ !!"x010"
    $ !!"x110"
    $ !!"x210"
    $ !!"x011"
    $ !!"x111"
    $ !!"x211"
    $ !!"x012"
    $ !!"x112"
    $ sym !!"x212"
    $ !!"x020"
    $ !!"x120"
    $ sym !!"x220"
    $ !!"x021"
    $ !!"x121"
    $ sym !!"x221"
    $ !!"x022"
    $ !!"x122")

let () = equal sym_apsym_xx222 sym_apsym_xx222'

let apsym_sym_apsym_x222, apsym_sym_apsym_xx222 =
  synth
    (refl
       ("y00"
        @-> "y01"
        @-> "y02"
        @-> "y10"
        @-> "y11"
        @-> "y12"
        @-> "y20"
        @-> "y21"
        @-> "y22"
        @-> sym !!"y22"
       <:> ("y00", !!"X")
           @=> ("y01", !!"X")
           @=> ("y02", id !!"X" !!"y00" !!"y01")
           @=> ("y10", !!"X")
           @=> ("y11", !!"X")
           @=> ("y12", id !!"X" !!"y10" !!"y11")
           @=> ("y20", id !!"X" !!"y00" !!"y10")
           @=> ("y21", id !!"X" !!"y01" !!"y11")
           @=> ( "y22",
                 refl (refl !!"X")
                 $ !!"y00"
                 $ !!"y01"
                 $ !!"y02"
                 $ !!"y10"
                 $ !!"y11"
                 $ !!"y12"
                 $ !!"y20"
                 $ !!"y21" )
           @=> (refl (refl !!"X")
               $ !!"y00"
               $ !!"y10"
               $ !!"y20"
               $ !!"y01"
               $ !!"y11"
               $ !!"y21"
               $ !!"y02"
               $ !!"y12"))
    $ !!"x000"
    $ !!"x100"
    $ !!"x200"
    $ !!"x001"
    $ !!"x101"
    $ !!"x201"
    $ !!"x002"
    $ !!"x102"
    $ sym !!"x202"
    $ !!"x010"
    $ !!"x110"
    $ !!"x210"
    $ !!"x011"
    $ !!"x111"
    $ !!"x211"
    $ !!"x012"
    $ !!"x112"
    $ sym !!"x212"
    $ !!"x020"
    $ !!"x120"
    $ sym !!"x220"
    $ !!"x021"
    $ !!"x121"
    $ sym !!"x221"
    $ !!"x022"
    $ !!"x122"
    $ sym
        (refl
           ("y00"
            @-> "y01"
            @-> "y02"
            @-> "y10"
            @-> "y11"
            @-> "y12"
            @-> "y20"
            @-> "y21"
            @-> "y22"
            @-> sym !!"y22"
           <:> ("y00", !!"X")
               @=> ("y01", !!"X")
               @=> ("y02", id !!"X" !!"y00" !!"y01")
               @=> ("y10", !!"X")
               @=> ("y11", !!"X")
               @=> ("y12", id !!"X" !!"y10" !!"y11")
               @=> ("y20", id !!"X" !!"y00" !!"y10")
               @=> ("y21", id !!"X" !!"y01" !!"y11")
               @=> ( "y22",
                     refl (refl !!"X")
                     $ !!"y00"
                     $ !!"y01"
                     $ !!"y02"
                     $ !!"y10"
                     $ !!"y11"
                     $ !!"y12"
                     $ !!"y20"
                     $ !!"y21" )
               @=> (refl (refl !!"X")
                   $ !!"y00"
                   $ !!"y10"
                   $ !!"y20"
                   $ !!"y01"
                   $ !!"y11"
                   $ !!"y21"
                   $ !!"y02"
                   $ !!"y12"))
        $ !!"x000"
        $ !!"x001"
        $ !!"x002"
        $ !!"x010"
        $ !!"x011"
        $ !!"x012"
        $ !!"x020"
        $ !!"x021"
        $ !!"x022"
        $ !!"x100"
        $ !!"x101"
        $ !!"x102"
        $ !!"x110"
        $ !!"x111"
        $ !!"x112"
        $ !!"x120"
        $ !!"x121"
        $ !!"x122"
        $ !!"x200"
        $ !!"x201"
        $ !!"x202"
        $ !!"x210"
        $ !!"x211"
        $ !!"x212"
        $ !!"x220"
        $ !!"x221"
        $ !!"x222"))

let apsym_sym_apsym_xx222', _ =
  synth
    (refl (refl (refl !!"X"))
    $ !!"x000"
    $ !!"x100"
    $ !!"x200"
    $ !!"x010"
    $ !!"x110"
    $ !!"x210"
    $ !!"x020"
    $ !!"x120"
    $ sym !!"x220"
    $ !!"x001"
    $ !!"x101"
    $ !!"x201"
    $ !!"x011"
    $ !!"x111"
    $ !!"x211"
    $ !!"x021"
    $ !!"x121"
    $ sym !!"x221"
    $ !!"x002"
    $ !!"x102"
    $ sym !!"x202"
    $ !!"x012"
    $ !!"x112"
    $ sym !!"x212"
    $ sym !!"x022"
    $ sym !!"x122")

let () = equal apsym_sym_apsym_xx222 apsym_sym_apsym_xx222'

(* Now we check that both sides have the same types and are equal *)

let () = equal sym_apsym_sym_xx222 apsym_sym_apsym_xx222
let () = equal sym_apsym_sym_x222 apsym_sym_apsym_x222

(* And they have an alternative, much simpler, degeneracy notation *)
let braid', braidty' = synth (!!"x222" $^ "321")
let () = equal sym_apsym_sym_xx222 braidty'
let () = equal sym_apsym_sym_x222 braid'
