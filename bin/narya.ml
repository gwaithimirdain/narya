(* This file implements the main executable, with parsing command-line flags and the ordinary and proofgeneral interactive modes. *)

open Bwd
open Util
open Core
open Parser
open React
open Lwt
open LTerm_text
open Top

let usage_msg = "narya [options] <file1> [<file2> ...]"
let interactive = ref false
let proofgeneral = ref false

(* Undocumented flag used for testing: interpret a given command-line string as if it were entered in interactive mode. *)
let fake_interacts : string Bwd.t ref = ref Emp

let speclist =
  [
    ("-interactive", Arg.Set interactive, "Enter interactive mode (also -i)");
    ("-i", Arg.Set interactive, "");
    ("-proofgeneral", Arg.Set proofgeneral, "Enter proof general interaction mode");
    ( "-exec",
      Arg.String (fun str -> inputs := Snoc (!inputs, `String str)),
      "Execute a string, after all files loaded (also -e)" );
    ("-e", Arg.String (fun str -> inputs := Snoc (!inputs, `String str)), "");
    ("-verbose", Arg.Set verbose, "Show verbose messages (also -v)");
    ("-v", Arg.Set verbose, "");
    ("-no-check", Arg.Clear execute, "Don't typecheck and execute code (only parse it)");
    ("-reformat", Arg.Set reformat, "Display reformatted code on stdout");
    ("-noncompact", Arg.Clear compact, "Reformat code noncompactly (default)");
    ("-compact", Arg.Set compact, "Reformat code compactly");
    ("-unicode", Arg.Set unicode, "Display and reformat code using Unicode for built-ins (default)");
    ("-ascii", Arg.Clear unicode, "Display and reformat code using ASCII for built-ins");
    ("-arity", Arg.Set_int arity, "Arity of parametricity (default = 2)");
    ( "-direction",
      Arg.String set_refls,
      "Names for parametricity direction and reflexivity (default = e,refl,Id)" );
    ("-internal", Arg.Set internal, "Set parametricity to internal (default)");
    ("-external", Arg.Clear internal, "Set parametricity to external");
    ("-discreteness", Arg.Set discreteness, "Enable discreteness");
    ("-source-only", Arg.Set source_only, "Load all files from source (ignore compiled versions)");
    ( "-dtt",
      Unit
        (fun () ->
          arity := 1;
          refl_char := 'd';
          refl_strings := [];
          internal := false),
      "Abbreviation for -arity 1 -direction d -external" );
    ("--help", Arg.Unit (fun () -> ()), "");
    ("-", Arg.Unit (fun () -> inputs := Snoc (!inputs, `Stdin)), "");
    ("-fake-interact", Arg.String (fun str -> fake_interacts := Snoc (!fake_interacts, str)), "");
  ]

(* Parse the command-line arguments and ensure that we have something to do. *)
let () =
  Arg.parse speclist anon_arg usage_msg;
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
        (* In interactive mode, we display all messages verbosely, and don't quit on fatal errors except for the Quit command. *)
        Reporter.try_with
          ~emit:(fun d -> Terminal.display ~output:stdout d)
          ~fatal:(fun d ->
            Terminal.display ~output:stdout d;
            match d.message with
            | Quit _ -> exit 0
            | _ -> ())
          (fun () -> do_command (Command.parse_single str));
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

(* In ProofGeneral interaction mode, the prompt is delimited by formfeeds, and commands are ended by a formfeed on a line by itself.  This prevents any possibility of collision with other input or output.  This doesn't require initialization. *)
let rec interact_pg () : unit =
  Format.printf "\x0C[narya]\x0C\n%!";
  try
    let buf = Buffer.create 20 in
    let str = ref "" in
    while !str <> "\x0C\n" do
      Buffer.add_string buf !str;
      let line = read_line () in
      str := if String.length line > 0 then line ^ "\n" else ""
    done;
    let cmd = Buffer.contents buf in
    let holes = ref Emp in
    ( Global.HolePos.run ~init:{ holes = Emp; offset = 0 } @@ fun () ->
      Reporter.try_with
      (* ProofGeneral sets TERM=dumb, but in fact it can display ANSI colors, so we tell Asai to override TERM and use colors unconditionally. *)
        ~emit:(fun d ->
          match d.message with
          | Hole _ -> holes := Snoc (!holes, d.message)
          | _ -> Terminal.display ~use_ansi:true ~output:stdout d)
        ~fatal:(fun d -> Terminal.display ~use_ansi:true ~output:stdout d)
        (fun () ->
          try
            do_command (Command.parse_single cmd);
            Format.printf "\x0C[goals]\x0C\n%!";
            Mbwd.miter
              (fun [ h ] ->
                Reporter.Code.default_text h Format.std_formatter;
                Format.printf "\n\n%!")
              [ !holes ];
            Format.printf "\x0C[data]\x0C\n%!";
            let st = Global.HolePos.get () in
            Mbwd.miter
              (fun [ (h, s, e) ] -> Format.printf "%d %d %d\n" h (s - st.offset) (e - st.offset))
              [ st.holes ]
          with Sys.Break -> Reporter.fatal Break) );
    interact_pg ()
  with End_of_file -> ()

let () =
  run_top @@ fun () ->
  Mbwd.miter
    (fun [ file ] ->
      let p, src = Parser.Command.Parse.start_parse (`File file) in
      Reporter.try_with ~emit:(Terminal.display ~output:stdout)
        ~fatal:(Terminal.display ~output:stdout) (fun () -> Execute.batch true [] p src))
    [ !fake_interacts ];
  if !interactive then Lwt_main.run (interact ())
  else if !proofgeneral then (
    Sys.catch_break true;
    interact_pg ())
