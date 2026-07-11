(* This file implements the main executable, with parsing command-line flags and the ordinary and proofgeneral interactive modes. *)

open Bwd
open Util
open Core
open Origin
open Parser
open React
open Lwt
open LTerm_text
open Print
open PPrint
open Top

type arity = [ `One of string | `Any ]

let usage_msg = "narya [options] <file1> [<file2> ...]"
let interactive = ref false
let proofgeneral = ref false
let show_version = ref false
let install_mode_theory = ref Modal.Trivial.install
let hott_forbidden : string option ref = ref None
let external_ok = ref false
let arity_ok : arity ref = ref `Any
let mode_theories = ref 0
let old_discreteness = ref false
let modes = ref ""
let modalities = ref ""

(* Undocumented flag used for testing: interpret a given file or command-line string as if it were entered in interactive mode. *)
let fake_interacts : string Bwd.t ref = ref Emp

(* Undocumented flag used for testing: always display ANSI colors even if the terminal doesn't support them. *)
let use_ansi = ref false

let speclist =
  [
    ("-version", Arg.Set show_version, "Show version and exit");
    ("-interactive", Arg.Set interactive, "Enter interactive mode (also -i)");
    ("-i", Arg.Set interactive, "");
    ("-proofgeneral", Arg.Set proofgeneral, "Enter proof general interaction mode");
    ( "-exec",
      Arg.String (fun str -> inputs := Snoc (!inputs, `String str)),
      "Execute a string, after all files loaded (also -e)" );
    ("-e", Arg.String (fun str -> inputs := Snoc (!inputs, `String str)), "");
    ("-verbose", Arg.Set verbose, "Show verbose messages (also -v)");
    ("-v", Arg.Set verbose, "");
    ( "-no-reformat",
      Arg.Clear reformat,
      "Don't automatically reformat files supplied on the command line" );
    ("-unicode", Arg.Set unicode, "Display and reformat code using Unicode for built-ins (default)");
    ("-ascii", Arg.Clear unicode, "Display and reformat code using ASCII for built-ins");
    ( "-hide-function-boundaries",
      Arg.Clear show_function_boundaries,
      "Hide implicit boundaries of higher-dimensional applications (default)" );
    ( "-show-function-boundaries",
      Arg.Set show_function_boundaries,
      "Display implicit boundaries of higher-dimensional applications" );
    ( "-hide-type-boundaries",
      Arg.Clear show_type_boundaries,
      "Hide implicit boundaries of instantiations of higher-dimensional types (default)" );
    ( "-show-type-boundaries",
      Arg.Set show_type_boundaries,
      "Display implicit boundaries of instantiations of higher-dimensional types" );
    ("-variables", Arg.String (fun str -> variables := Some str), "Default variable names");
    ("-arity", Arg.Set_int arity, "Arity of parametricity (default = 2)");
    ( "-direction",
      Arg.String set_refls,
      "Names for parametricity direction and reflexivity (default = e,refl,Id)" );
    ("-internal", Arg.Set internal, "Set parametricity to internal (default)");
    ("-external", Arg.Clear internal, "Set parametricity to external");
    ( "-parametric",
      Arg.Clear hott,
      "Switch from higher observational type theory (fibrancy) to parametricity" );
    ("-hott", Arg.Set hott_deprecated, "");
    ("-deprecated-discreteness", Arg.Set discreteness, "Enable discrete datatypes (deprecated)");
    ("-discreteness", Arg.Set old_discreteness, "");
    ("-source-only", Arg.Set source_only, "Load all files from source (ignore compiled versions)");
    (* Mode theories *)
    ( "-coreflector",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Coreflector.install;
          mode_theories := !mode_theories + 1),
      "Select the coreflector mode theory" );
    ( "-crisp",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Coreflector.install;
          mode_theories := !mode_theories + 1),
      "alias of -coreflector" );
    ( "-discrete-coreflector",
      Arg.Unit
        (fun () ->
          hott_forbidden := Some "-discrete-coreflector";
          external_ok := true;
          install_mode_theory := Modal.Discrete_coreflector.install;
          mode_theories := !mode_theories + 1),
      "Select the nonparametric coreflector mode theory (requires -parametric, allows -external)" );
    ( "-reflector",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Reflector.install;
          mode_theories := !mode_theories + 1),
      "Select the reflector mode theory" );
    ( "-spatial",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Spatial.install;
          mode_theories := !mode_theories + 1),
      "Select the spatial mode theory (coreflector ♭ left adjoint to reflector ♯)" );
    ( "-discrete-spatial",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Discrete_spatial.install;
          hott_forbidden := Some "-discrete-spatial";
          mode_theories := !mode_theories + 1),
      "Select the spatial mode theory with discrete coreflector (requires -parametric)" );
    ( "-functor",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Functor.install;
          mode_theories := !mode_theories + 1),
      "Select the functor mode theory" );
    ( "-transparent-functor",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Transparent_functor.install;
          mode_theories := !mode_theories + 1),
      "Select the transparent functor mode theory" );
    ( "-discrete-functor",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Discrete_functor.install;
          hott_forbidden := Some "-discrete-functor";
          mode_theories := !mode_theories + 1),
      "Select the functor mode theory with discrete domain mode (requires -parametric)" );
    ( "-composed-functors",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Composed_functors.install;
          mode_theories := !mode_theories + 1),
      "Select the composed functors mode theory" );
    ( "-coreflection",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Coreflection.install;
          mode_theories := !mode_theories + 1),
      "Select the coreflection mode theory" );
    ( "-discrete-coreflection",
      Arg.Unit
        (fun () ->
          hott_forbidden := Some "-discrete-coreflector";
          external_ok := true;
          install_mode_theory := Modal.Discrete_coreflection.install;
          mode_theories := !mode_theories + 1),
      "Select the nonparametric coreflection mode theory (requires -parametric, allows -external)"
    );
    ( "-tconn",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Tconn.install;
          mode_theories := !mode_theories + 1),
      "Select the totally connected geometric morphism mode theory" );
    ( "-discrete-tconn",
      Arg.Unit
        (fun () ->
          hott_forbidden := Some "-discrete-tconn";
          external_ok := true;
          arity_ok := `One "-discrete-tconn";
          install_mode_theory := Modal.Discrete_tconn.install;
          mode_theories := !mode_theories + 1),
      "Select the discrete tconn mode theory (requires -parametric and -arity 1, allows -external)"
    );
    ( "-pseudo-tconn",
      Arg.Unit
        (fun () ->
          install_mode_theory := Modal.Pseudo_tconn.install;
          mode_theories := !mode_theories + 1),
      "Select the pseudo totally connected geometric morphism mode theory" );
    ( "-discrete-pseudo-tconn",
      Arg.Unit
        (fun () ->
          hott_forbidden := Some "-discrete-pseudo-tconn";
          external_ok := true;
          install_mode_theory := Modal.Discrete_pseudo_tconn.install;
          mode_theories := !mode_theories + 1),
      "Select the discrete pseudo-tconn mode theory (requires -parametric, allows -external)" );
    ( "-dtt",
      Unit
        (fun () ->
          hott := false;
          arity := 1;
          refl_char := 'd';
          refl_names := [];
          internal := false;
          external_ok := true;
          arity_ok := `One "-dtt";
          hott_forbidden := Some "-dtt";
          install_mode_theory := Modal.Discrete_tconn.install;
          mode_theories := !mode_theories + 1),
      "Abbreviation for -parametric -arity 1 -direction d -external -discrete-tconn" );
    ("-modes", Arg.Set_string modes, "set the names of modes");
    ("-modalities", Arg.Set_string modalities, "set the names of modalities");
    ("--help", Arg.Unit (fun () -> ()), "");
    ("-", Arg.Unit (fun () -> inputs := Snoc (!inputs, `Stdin)), "");
    ("-fake-interact", Arg.String (fun str -> fake_interacts := Snoc (!fake_interacts, str)), "");
    ("-number-metas", Arg.Set number_metas, "");
    ("-anonymous-metas", Arg.Clear number_metas, "");
    ("-parenthesize-arguments", Arg.Set parenthesize_arguments, "");
    ("-juxtapose-arguments", Arg.Clear parenthesize_arguments, "");
    ("-remove-spaces", Arg.Clear extra_spaces, "");
    ("-use-ansi", Arg.Set use_ansi, "");
  ]

(* Parse the command-line arguments and ensure that we have something to do. *)
let () =
  Arg.parse speclist anon_arg usage_msg;
  if !show_version then (
    print_endline (String.trim [%blob "version.txt"]);
    exit 0);
  if !old_discreteness then (
    Printf.eprintf
      "-discreteness is deprecated; use discrete modalities instead.\nYou can use -deprecated-discreteness while porting old code.";
    exit 1);
  if !mode_theories > 1 then (
    Printf.fprintf stderr "too many mode theories! specify only one.";
    exit 1);
  (match (!hott, !hott_forbidden) with
  | true, Some thy ->
      Printf.fprintf stderr "%s requires -parametric\n" thy;
      exit 1
  | _ -> ());
  if (not !internal) && !hott then (
    Printf.fprintf stderr "-external requires -parametric\n";
    exit 1);
  if (not !internal) && not !external_ok then (
    Printf.fprintf stderr "-external requires a suitable mode theory\n";
    exit 1);
  (match (!arity_ok, !arity) with
  | `One _, 1 -> ()
  | `One str, _ ->
      Printf.fprintf stderr "%s requires -arity 1\n" str;
      exit 1
  | _ -> ());
  if
    Bwd.is_empty !inputs
    && (not !interactive)
    && (not !proofgeneral)
    && Bwd.is_empty !fake_interacts
  then (
    Printf.fprintf stderr "No input files specified\n";
    Arg.usage speclist usage_msg;
    exit 1)

let ( let* ) f o = Lwt.bind f o

class read_line terminal history prompt =
  object (self)
    inherit LTerm_read_line.read_line ~history ()
    inherit [Zed_string.t] LTerm_read_line.term terminal
    method! show_box = false
    initializer self#set_prompt (S.const (eval [ B_underline true; S prompt; B_underline false ]))
  end

(* Run the Read-Eval-Print Loop for interactive mode using Zed, Lwt, and Readline. *)
let rec repl terminal history buf =
  let buf, prompt =
    match buf with
    | Some buf -> (buf, "")
    | None -> (Buffer.create 70, "narya\n") in
  (* Read lines and accumulate their contents until we find a blank line, indicating that the command is over. *)
  let* command =
    Lwt.catch
      (fun () ->
        let rl = new read_line terminal (LTerm_history.contents history) prompt in
        rl#run >|= fun command -> Some command)
      (function
        | Sys.Break -> return None
        | exn -> Lwt.fail exn) in
  match command with
  | Some command ->
      let str = Zed_string.to_utf8 command in
      if str = "" then (
        let str = Buffer.contents buf in
        let* () = Lwt_io.flush Lwt_io.stdout in
        let use_ansi = if !use_ansi then Some true else None in
        (* In interactive mode, we display all messages verbosely, and don't quit on fatal errors except for the Quit command. *)
        ( Reporter.try_with
            ~emit:(fun d -> Reporter.display ?use_ansi ~output:stdout d)
            ~fatal:(fun d ->
              Reporter.display ?use_ansi ~output:stdout d;
              match d.message with
              | Quit _ -> exit 0
              | _ -> ())
        @@ fun () ->
          match Command.parse_single str with
          | _, Some cmd ->
              (* We ignore the hole data, which is only for ProofGeneral. *)
              let _ = Execute.execute_command cmd in
              Global.notify_holes ()
          | _ -> () );
        LTerm_history.add history (Zed_string.of_utf8 (String.trim str));
        repl terminal history None)
      else (
        Buffer.add_string buf str;
        Buffer.add_char buf '\n';
        repl terminal history (Some buf))
  | None -> repl terminal history None

let history_file = Unix.getenv "HOME" ^ "/.narya_history"

(* Initialize LTerm and Lwt for the interactive mode REPL. *)
let interact () =
  let* () = LTerm_inputrc.load () in
  let history = LTerm_history.create [] in
  let* () = LTerm_history.load history history_file in
  Lwt.catch
    (fun () ->
      let* terminal = Lazy.force LTerm.stdout in
      repl terminal history None)
    (function
      | LTerm_read_line.Interrupt ->
          let* () = LTerm_history.save history history_file in
          Lwt.return ()
      | exn ->
          let* () = LTerm_history.save history history_file in
          Lwt.fail exn)

let rec print_error_locs (d : Reporter.Code.t Asai.Diagnostic.t) =
  match d.message with
  | Accumulated (_name, msgs) -> Mbwd.miter (fun [ e ] -> print_error_locs e) [ msgs ]
  | _ -> (
      match d.explanation.loc with
      | Some loc -> (
          match Asai.Range.view loc with
          | `Range (s, e) -> Format.printf "%d %d\n" s.offset e.offset
          | `End_of_file p -> Format.printf "%d\n" p.offset)
      | None -> ())

(* In ProofGeneral interaction mode, the prompt is delimited by formfeeds, and commands are ended by a formfeed on a line by itself.  This prevents any possibility of collision with other input or output.  This doesn't require initialization. *)
let rec interact_pg () : unit =
  Format.printf "\x0C[narya]\x0C\n%!";
  try
    let buf = Buffer.create 20 in
    let atstart = ref true in
    let str = ref "" in
    while !str <> "\x0C\n" do
      Buffer.add_string buf !str;
      let line = read_line () in
      (* Sometimes the command we get has a blank line at the beginning and sometimes it doesn't.  I don't understand why. *)
      if (not !atstart) || line <> "" then (
        str := line ^ "\n";
        atstart := false)
    done;
    let cmd = Buffer.contents buf in
    let holes = ref Emp in
    Display.modify (fun s -> { s with holes = `With_number });
    Reporter.try_with
    (* ProofGeneral sets TERM=dumb, but in fact it can display ANSI colors, so we tell Asai to override TERM and use colors unconditionally. *)
      ~emit:(fun d ->
        match d.message with
        | Hole _ -> holes := Snoc (!holes, d.message)
        | _ -> Reporter.display ~use_ansi:true ~output:stdout d)
      ~fatal:(fun d ->
        Reporter.display ~use_ansi:true ~output:stdout d;
        Format.printf "\x0C[errors]\x0C\n%!";
        print_error_locs d)
      (fun () ->
        try
          match Command.parse_single cmd with
          | _, None -> ()
          | prews, Some cmd ->
              let offset, newholes = Execute.execute_command cmd in
              let offset = Option.value ~default:0 offset in
              Global.notify_holes ();
              Format.printf "\x0C[goals]\x0C\n%!";
              Mbwd.miter
                (fun [ h ] ->
                  Reporter.Code.default_text h Format.std_formatter;
                  Format.printf "\n\n%!")
                [ !holes ];
              Format.printf "\x0C[data]\x0C\n%!";
              if Parser.Command.parenthesized cmd then Format.printf "parenthesized\n"
              else Format.printf "unparenthesized\n";
              Format.printf "%s\n" (Origin.to_string (Origin.current ()));
              Mlist.miter
                (fun [ (h, s, e) ] -> Format.printf "%d %d %d\n" h (s - offset) (e - offset))
                [ newholes ];
              Format.printf "\x0C[reformat]\x0C\n%!";
              let pcmd, wcmd = Parser.Command.pp_command cmd in
              ToChannel.pretty 1.0 (Display.columns ()) stdout
                (pp_ws `None prews ^^ pcmd ^^ pp_ws `None wcmd)
        with Sys.Break -> Reporter.fatal Break);
    interact_pg ()
  with End_of_file -> ()

let () =
  try
    let modes = List.filter (fun x -> x <> "") (String.split_on_char ',' !modes) in
    let modalities = List.filter (fun x -> x <> "") (String.split_on_char ',' !modalities) in
    !install_mode_theory modes modalities;
    let use_ansi = if !use_ansi then Some true else None in
    run_top ?use_ansi ~install_hott:Hott.install @@ fun () ->
    (* Note: run_top executes the input files, so here we only have to do the interaction. *)
    Mbwd.miter
      (fun [ file ] ->
        let source : Asai.Range.source =
          if try FileUtil.test Is_file file with _ -> false then `File file
          else `String { title = Some "command line fake-interact"; content = file } in
        let p, src = Parser.Command.Parse.start_parse source in
        Reporter.try_with ~emit:(Reporter.display ?use_ansi ~output:stdout)
          ~fatal:(Reporter.display ?use_ansi ~output:stdout) (fun () ->
            Execute.batch None p src `None []))
      [ !fake_interacts ];
    if !interactive then Lwt_main.run (interact ())
    else if !proofgeneral then (
      Sys.catch_break true;
      interact_pg ())
  with Top.Exit -> exit 1
