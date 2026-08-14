(* This file contains all the code for the main executable that doesn't specify how we interact with the user (such as parsing command-line arguments and running an interactive REPL).  Thus, it can be shared between the ordinary executable and any variants like the in-browser javascript version. *)

open Bwd
open Util
open Core
open Origin
open Reporter
open Readback
open Parser
module Execute = Execute

(* Global flags, as set for instance by command-line arguments. *)
let inputs : [ `String of string | `File of string | `Stdin ] Bwd.t ref = ref Emp
let anon_arg filename = inputs := Snoc (!inputs, `File filename)
let verbose = ref false
let reformat = ref true
let unicode = ref true

(* The type theory options given by command-line flags.  These constrain but do not determine the options in force: a source file specifies a complete set of them, which these must agree with.  See Core.Options. *)
let cmdline_options : Options.partial ref = ref Options.empty
let hott_deprecated = ref false

(* Which type theory flags were given on the command line, in the order they were written.  Setting the type theory from the command line is deprecated in favor of "option" commands in the source, which is where the type theory belongs: it is a property of the code, not of an invocation.  A run with no source file at all can still set it, either with -e "option ..." or, in interactive and ProofGeneral mode, by entering the "option" command before anything else. *)
let deprecated_flags : string Bwd.t ref = ref Emp

let note_deprecated_flag f =
  if not (Bwd.exists (fun x -> x = f) !deprecated_flags) then
    deprecated_flags := Snoc (!deprecated_flags, f)

(* The deprecated strict parametric discreteness is not one of the type theory options proper (see Core.Options): it is set only from the command line and is not subject to the agreement check, so that a library can still be loaded both with and without it while old code is ported. *)
let discreteness = ref false
let source_only = ref false
let number_metas = ref true
let parenthesize_arguments = ref false
let extra_spaces = ref true
let show_function_boundaries = ref false
let show_type_boundaries = ref false
let show_unique_keys = ref false
let variables = ref None

(* Helpers for the command-line flags that set individual type theory options. *)
let set_option f = cmdline_options := f !cmdline_options
let set_arity n = set_option (fun o -> { o with parity = Some n })
let set_hott b = set_option (fun o -> { o with phott = Some b })
let set_internal b = set_option (fun o -> { o with pinternal = Some b })
let set_theory name = set_option (fun o -> { o with ptheory = Some name })

let set_names f str =
  let xs = List.filter (fun x -> x <> "") (String.split_on_char ',' str) in
  set_option (fun o -> f o xs)

(* Given a string like "r,refl,Id" as in a command-line "-direction" argument, set the direction character and the reflexivity names. *)
let set_refls str =
  match String.split_on_char ',' str with
  | [] -> raise (Failure "Empty direction names")
  | c :: _ when String.length c <> 1 || c.[0] < 'a' || c.[0] > 'z' ->
      raise (Failure "Direction name must be a single lowercase letter")
  | c :: names -> set_option (fun o -> { o with prefl_char = Some c.[0]; prefl_names = Some names })

(* This exception is raised when a fatal error occurs in loading the non-interactive inputs.  The caller should catch it and perform an appropriate kind of "exit".  *)
exception Exit

(* Whether a user-supplied name is usable as a single identifier token: nonempty, not starting with an underscore or a digit, and containing no dots or whitespace (which the lexer would split into separate tokens). *)
let valid_name s =
  s <> ""
  && s.[0] <> '_'
  && (not (s.[0] >= '0' && s.[0] <= '9'))
  && (not (String.contains s '.'))
  && not (String.exists (fun c -> c = ' ' || c = '\t' || c = '\n' || c = '\r') s)

(* The distinct elements that appear more than once in a list. *)
let duplicates names =
  let seen = Hashtbl.create 16 and dups = Hashtbl.create 16 in
  List.iter
    (fun n -> if Hashtbl.mem seen n then Hashtbl.replace dups n () else Hashtbl.add seen n ())
    names;
  Hashtbl.fold (fun n () acc -> n :: acc) dups []

(* Whether the nonempty string [s] can be written as a concatenation of one or more of the strings in [parts]. *)
let is_concatenation s parts =
  let parts = List.filter (fun p -> p <> "") parts in
  let n = String.length s in
  let dp = Array.make (n + 1) false in
  dp.(0) <- true;
  for i = 1 to n do
    List.iter
      (fun p ->
        let lp = String.length p in
        if i >= lp && dp.(i - lp) && String.sub s (i - lp) lp = p then dp.(i) <- true)
      parts
  done;
  n > 0 && dp.(n)

(* Sanity-check the names used to rename modes, modalities, and modal cells.  The three list arguments are the user-supplied names (empty if that kind was not renamed); the effective names of each kind (user-supplied ones plus any left at their defaults) are read back from the installed mode theory, so this must be called *after* installing it.  Because renaming is all-or-nothing per kind, checks that could be triggered by a theory's default names are only run for the kinds the user actually renamed. *)
let check_names modes modalities modalcells =
  let errors = ref [] in
  let err fmt = Printf.ksprintf (fun s -> errors := s :: !errors) fmt in
  (* 6. All user-supplied names must be valid single identifiers. *)
  List.iter
    (fun (kind, names) ->
      List.iter
        (fun name ->
          if not (valid_name name) then err "%s name '%s' is not a valid identifier" kind name)
        names)
    [ ("mode", modes); ("modality", modalities); ("modal cell", modalcells) ];
  (* 1. No user-supplied name may be a reserved word.  This is essential for modes, which appear in term position; we apply it to modalities and cells too, since a keyword there would also confuse the lexer. *)
  List.iter
    (fun (kind, names) ->
      List.iter
        (fun name ->
          if Option.is_some (Lexer.get_reserved_word name) then
            err "%s name '%s' is a reserved word" kind name)
        names)
    [ ("mode", modes); ("modality", modalities); ("modal cell", modalcells) ];
  let eff_modalities = Modal.Modality.all_names () in
  let eff_cells = Modal.Modalcell.all_names () in
  (* Deduplicated cell names, for the cross-checks below that would otherwise report a duplicated name once per occurrence. *)
  let uniq_cells = List.sort_uniq compare eff_cells in
  (* 7. No two modes may share a name. *)
  if modes <> [] then
    List.iter
      (fun n -> err "duplicate mode name '%s'" n)
      (duplicates (List.map fst (Modal.Mode.all ())));
  (* 2. No two modalities may share a name. *)
  if modalities <> [] then
    List.iter (fun n -> err "duplicate modality name '%s'" n) (duplicates eff_modalities);
  (* 3. No two modal cells may share a name. *)
  if modalcells <> [] then
    List.iter (fun n -> err "duplicate modal cell name '%s'" n) (duplicates eff_cells);
  (* 4. No modal cell may share a name with a modality, since the two are mixed in the parsing and printing of keys. *)
  if modalities <> [] || modalcells <> [] then
    List.iter
      (fun c ->
        if List.mem c eff_modalities then err "modal cell name '%s' is also a modality name" c)
      uniq_cells;
  (* 5. When modalities are printed as single characters with no separators, a modal cell name that is a concatenation of modality names would be ambiguous. *)
  if modalcells <> [] && Modal.Modality.one_char () then
    List.iter
      (fun c ->
        if (not (List.mem c eff_modalities)) && is_concatenation c eff_modalities then
          err
            "modal cell name '%s' is a concatenation of modality names, which is ambiguous when modalities are single characters"
            c)
      uniq_cells;
  match List.rev !errors with
  | [] -> ()
  | errs -> Reporter.fatal (Invalid_options errs)

(* Actually install a complete set of type theory options, fixing the theory for the rest of the run.  This is called by Execute.fix_options, just before the first command that isn't an "option" command.  Everything here is global mutable state rather than an effect handler, precisely because by this point we are already deep inside the handlers that would otherwise have had to wrap it. *)
let install_options ~install_hott (opts : Options.t) =
  (match Options.Theories.find opts.theory with
  (* The installation functions signal a wrong number of user-supplied names by raising Failure.  That's a user error in the options, not a bug, so we report it as one; otherwise the enclosing handler would turn it into an anomaly. *)
  | Some e -> (
      try e.install opts.modes opts.modalities opts.modalcells
      with Failure msg -> Reporter.fatal (Invalid_options [ msg ]))
  | None ->
      Reporter.fatal
        (Invalid_options [ "unknown mode theory '" ^ Options.Theories.to_string opts.theory ^ "'" ]));
  check_names opts.modes opts.modalities opts.modalcells;
  (* The universe notations are named after the modes, so they can only be installed once the mode theory is. *)
  Parser.Builtins.install_universes ();
  Core.Discrete.set !discreteness;
  Dim.Endpoints.set ~arity:opts.arity ~refl_char:opts.refl_char ~refl_names:opts.refl_names
    ~internal:opts.internal ~hott:opts.hott;
  Options.set_installed opts;
  if opts.hott then install_hott () else Check.gel_ok := true

(* This function is called to wrap whatever "interactive mode" is implemented by the caller.  It sets up the environment and all the effect handlers based on the global flags, loads all the files and strings specified in the global flags, and then runs the callback. *)
let run_top ?use_ansi ?onechar_ops ?digit_vars ?ascii_symbols ?(interactive = true) ~install_hott f
    =
  Check.Oracle.run ~ask:(fun _ -> Ok ()) @@ fun () ->
  Lexer.Specials.run ?onechar_ops ?ascii_symbols ?digit_vars @@ fun () ->
  Parser.Unparse.install ();
  Origin.run @@ fun () ->
  (* Only the builtins that don't depend on the mode theory can be installed now; the universe notations wait until the options are fixed. *)
  Parser.Builtins.install ();
  Parser.Scope.Mod.run @@ fun () ->
  Display.run
    ~init:
      {
        chars = (if !unicode then `Unicode else `ASCII);
        metas = (if !number_metas then `Numbered else `Anonymous);
        argstyle = (if !parenthesize_arguments then `Parens else `Spaces);
        spacing = (if !extra_spaces then `Wide else `Narrow);
        function_boundaries = (if !show_function_boundaries then `Show else `Hide);
        type_boundaries = (if !show_type_boundaries then `Show else `Hide);
        unique_keys = (if !show_unique_keys then `Show else `Hide);
        holes = `Without_number;
        variables =
          (match !variables with
          | Some xs -> String.split_on_char ',' xs
          | None -> Display.default.variables);
      }
  @@ fun () ->
  Annotate.run @@ fun () ->
  Readback.Displaying.run ~env:false @@ fun () ->
  Core.Positivity.run @@ fun () ->
  (* A temporary Reporter.run to report these errors *)
  ( Reporter.run
      ~emit:(fun d ->
        if !verbose || d.severity = Error || d.severity = Warning then
          Reporter.display ?use_ansi ~output:stderr d)
      ~fatal:(fun d ->
        Reporter.display ?use_ansi ~output:stderr d;
        raise Exit)
  @@ fun () ->
    if !hott_deprecated then Reporter.emit (Deprecated "-hott (this is now the default)");
    (match !deprecated_flags with
    | Emp -> ()
    | flags ->
        Reporter.emit
          (Deprecated
             (Printf.sprintf
                "setting the type theory on the command line (%s); use 'option' commands in the source file instead, or -e \"option ...\" when there is no file"
                (String.concat " " (Bwd.to_list flags)))));
    (* The argument of -variables must be a nonempty comma-separated list of valid variable names. *)
    match !variables with
    | Some str ->
        List.iter
          (fun x ->
            Reporter.try_with ~fatal:(fun _ -> Reporter.fatal (Invalid_variable [ x ])) @@ fun () ->
            match Lexer.single x with
            (* We require y = x so that names with surrounding whitespace, which the lexer would skip over, are also rejected, since the raw string is what gets stored in the Display state. *)
            | Some (Ident [ y ]) when y = x && Lexer.valid_var y -> ()
            | _ -> Reporter.fatal (Invalid_variable [ x ]))
          (String.split_on_char ',' str)
    | None -> () );
  (* The type theory itself isn't installed here: it isn't known until the leading "option" commands of the first source have been read.  See [install_options] below and Execute.fix_options. *)
  Reporter.run
    ~emit:(fun d ->
      if !verbose || d.severity = Error || d.severity = Warning then
        Reporter.display ?use_ansi ~output:stderr d)
    ~fatal:(fun d ->
      Reporter.display ?use_ansi ~output:stderr d;
      raise Exit)
  @@ fun () ->
  (* Some anomalies are thrown as Failure instead because they're in code that's defined before Reporter. *)
  try
    (* Printing errors that happen outside of any other error should be reported as fatal errors on their own. *)
    Reporter.Code.PrintingError.run ~env:(fun d -> fatal d) @@ fun () ->
    let top_files =
      Bwd.fold_right
        (fun input acc ->
          match input with
          | `File file -> FilePath.make_absolute (Sys.getcwd ()) file :: acc
          | _ -> acc)
        !inputs [] in
    Subtype.run @@ fun () ->
    Execute.Flags.run
      ~env:
        {
          cmdline = !cmdline_options;
          install = install_options ~install_hott;
          source_only = !source_only;
          top_files;
          reformat = !reformat;
        }
    @@ fun () ->
    Execute.Loaded.run @@ fun () ->
    Execute.Loading.run
      ~init:
        {
          cwd = Sys.getcwd ();
          parents = Emp;
          imports = Emp;
          actions = false;
          source = "the command line";
          options = Options.empty;
          options_fixed = false;
          started = false;
          (* Strings and interactive input, unlike files, only constrain the options they mention. *)
          total = false;
        }
    @@ fun () ->
    Mbwd.miter
      (fun [ input ] ->
        let source =
          match input with
          | `File filename ->
              let _ = Execute.load_file filename true in
              `File filename
          | `Stdin ->
              let content = In_channel.input_all stdin in
              let _ = Execute.load_string "stdin" content in
              `Stdin
          (* Command-line strings have all the previous units loaded without needing to import them. *)
          | `String content ->
              let _ =
                Execute.load_string ~init_visible:(Execute.Loaded.get_scope ())
                  "command-line exec string" content in
              `String in
        if Global.unsolved_holes () > 0 then Reporter.fatal (Open_holes_remaining source))
      [ !inputs ];
    (* If no input has fixed the type theory yet and we aren't about to enter an interactive loop -- during the higher observational bootstrap, say -- then the command-line flags determine it, and this is where they are validated.  When we *are* entering an interactive loop we leave the options open, so that an "option" block at the top of the buffer being processed can still fix them; see Execute.interactive_options. *)
    if not interactive then Execute.fix_options ();
    (* Interactive mode also has all the other units loaded.  Note that this should affect the "Top" origin. *)
    Scope.set_visible (Execute.Loaded.get_scope ());
    if interactive then Origin.set_interactive ();
    f ()
  with Failure str -> fatal (Anomaly ("failure: " ^ str))

(* Some applications may not be able to put their entire main loop inside a single call to "run_top".  Specifically, js_of_ocaml applications may need to return control to the browser periodically, but want to maintain the state that's normally stored in the effect handlers wrapped by run_top.  To accommodate this, we implement a "pausable" coroutine version of run_top, using effects, that saves a continuation inside all the handlers and returns to it whenever needed.  When our run_top callback finishes a single command, it yields control by performing the "Yield" effect, passing the output of the command it just executed.  The handler for this effect doesn't immediately continue, but stores the continuation in a global variable and returns control to the caller.  Then when we need to re-enter run_top, the continuation is resumed, passing it the code to be executed. *)

module Pauseable (R : Signatures.Type) = struct
  open Effect.Deep

  type _ Effect.t += Yield : R.t -> (unit -> R.t) Effect.t

  exception Halt

  (* The stored continuation, which points into the callback inside run_top. *)
  let cont : (unit -> R.t, R.t) continuation option ref = ref None

  (* The coroutine.  This calls itself with an infinite recursion and so never actually returns in an ordinary way, only by performing effects.  But it is declared to have a return type of R.t, to match that of the effects. *)
  let rec corun_top (f : unit -> R.t) : R.t =
    (* The "Yield" effect returns control to the caller until we are continued.  At that point execution resumes here with a new callback, which we then pass off to ourselves recursively. *)
    corun_top (Effect.perform (Yield (f ())))

  (* Whenever we need to restart, we discontinue the continuation, if any, and reset it. *)
  let halt () =
    try
      match !cont with
      | Some k ->
          let _ = discontinue k Halt in
          ()
      | None -> ()
    with Halt -> cont := None

  (* We initialize the setup by calling run_top inside the effect handler. *)
  let init ?use_ansi ?onechar_ops ?digit_vars ?ascii_symbols ~install_hott f =
    (* First we discontinue any existing continuation, to avoid leaks. *)
    halt ();
    try
      run_top ?use_ansi ?onechar_ops ?digit_vars ?ascii_symbols ~install_hott @@ fun () ->
      corun_top f
    with effect Yield output, k ->
      cont := Some k;
      output

  (* After startup, the caller calls "next" with a callback to be executed inside the run_top handlers and return a value. *)
  let next (f : unit -> R.t) : R.t =
    continue (!cont <|> Anomaly "missing continuation in Pauseable.next") f
end
