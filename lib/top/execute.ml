open Bwd
open Util
open Core
open Origin
open Reporter
open Parser
open PPrint
open Print
module Trie = Yuujinchou.Trie

(* Execution of files (and strings), including marshaling and unmarshaling, and managing file identifiers and imports. *)

(* Compiled files are tagged with the git hash of the commit, so they will only be loaded by Narya built from the exact same commit.  This is overkill, since most commits don't change the marshaling format; but it guarantees automatically that we never try to load a file that has a different marshaling format, thereby avoiding segmentation faults.  A version of -1 means that we don't know our git commit, and therefore we never load or save compiled files. *)
let __COMPILE_VERSION__ =
  Option.value ~default:(-1) (int_of_string_opt ("0x" ^ [%blob "version.txt"]))

(* This state module is for data that gets restarted when loading a new file. *)
module Loadstate = struct
  type t = {
    (* The current directory.  Used for making filenames absolute. *)
    cwd : FilePath.filename;
    (* All files whose loading is currently in progress, i.e. the path of imports that led us to the current file.  Used to check for circular imports. *)
    parents : FilePath.filename Bwd.t;
    (* All the files imported so far by the current file, *transitively* (that is, files it imports, and files *they* import, etc.).  Stored in compiled files to ensure they are recompiled whenever any dependencies change, and for linking purposes. *)
    imports : (File.t * FilePath.filename) Bwd.t;
    (* Whether the current file has performed any effectual actions like 'echo'.  Stored in compiled files to produce a warning. *)
    actions : bool;
    (* A description of the current source, for error messages about conflicting options. *)
    source : string;
    (* The type theory options declared so far by the leading "option" commands of the current source. *)
    options : Options.partial;
    (* Whether the options of the current source have been fixed, so that its "option" block is over. *)
    options_fixed : bool;
    (* Whether the current source has executed a command that isn't an "option", after which a further "option" command is an error. *)
    started : bool;
    (* Whether the current source specifies a *total* set of options, i.e. whether its silence about an option is an assertion of the default.  True for files, which are complete self-describing artifacts; false for the command line, -e strings, and interactive input, which only constrain the options they mention.  See Core.Options. *)
    total : bool;
  }
end

module Loading = struct
  include State.Make (Loadstate)

  let run ~init f =
    run ~init @@ fun () ->
    try f ()
    with effect Parser.Command.Chdir dir, k ->
      let cwd = FilePath.make_absolute (get ()).cwd dir in
      modify (fun s -> { s with cwd });
      Effect.Deep.continue k cwd
end

let () =
  Loading.register_printer (function
    | `Get -> Some "unhandled Loading.get effect"
    | `Set _ -> Some "unhandled Loading.set effect")

(* This reader module is for data that's supplied by the executable, mostly from the command-line, and doesn't change. *)
module FlagData = struct
  type t = {
    (* The type theory options specified by command-line flags.  Unlike a source file, the command line specifies only a *partial* set of options: it constrains the ones it mentions and says nothing about the rest.  So when a file is loaded, these can only agree with the file or conflict with it; they determine the type theory only when there is no file, as with -e, stdin, or interactive mode. *)
    cmdline : Options.partial;
    (* Fix the type theory to the given options.  This is a callback because installing higher observational type theory means loading its bootstrap, which lives in a library that depends on this one. *)
    install : Options.t -> unit;
    (* Load files from source only (not compiled versions). *)
    source_only : bool;
    (* All the filenames given explicitly on the command line. *)
    top_files : string list;
    (* Whether to reformat explicitly-loaded files *)
    reformat : bool;
  }
end

module Flags = Algaeff.Reader.Make (FlagData)

let () = Flags.register_printer (function `Read -> Some "unhandled Flags.read effect")

module Loaded = struct
  type data = {
    trie : Scope.trie;
    globals : Global.origin_entry;
    file : File.t;
    old_imports : (File.t * FilePath.filename) Bwd.t;
    explicit : bool;
  }

  type _ Effect.t +=
    | Add_to_files : FilePath.filename * data -> unit Effect.t
    | Get_file : FilePath.filename -> (data * float) option Effect.t
    | Add_to_scope : Scope.trie -> unit Effect.t
    | Get_scope : Scope.trie Effect.t

  open Effect.Deep

  let run f =
    (* All the files that have been loaded so far in this run of the program, along with their export namespaces, file identifiers, files that *they* import transitively, modification time when they were loaded, and whether they were explicitly invoked on the command line. *)
    let loaded_files : (FilePath.filename, data * float) Hashtbl.t = Hashtbl.create 20 in
    (* The complete merged namespace of all the files explicitly given on the command line so far.  Imported into -e and -i.  We compute it lazily because if there is no -e or -i we don't need it.  (And also so that we won't try to read the flags before they're set.)  It starts as the "current" namespace, which should be the top-level one. *)
    let loaded_contents : Scope.trie Lazy.t ref = ref (Lazy.from_val (Scope.get_visible ())) in
    try f () with
    | effect Add_to_files (file, data), k ->
        let mtime = (FileUtil.stat file).modification_time in
        Hashtbl.add loaded_files file (data, mtime);
        continue k ()
    | effect Get_file file, k -> continue k (Hashtbl.find_opt loaded_files file)
    | effect Add_to_scope trie, k ->
        let old = !loaded_contents in
        loaded_contents := lazy (Scope.Mod.union ~prefix:Emp (Lazy.force old) trie);
        continue k ()
    (* Add something to the complete merged namespace. *)
    | effect Get_scope, k -> continue k (Lazy.force !loaded_contents)

  let add_to_scope trie = Effect.perform (Add_to_scope trie)
  let get_scope () = Effect.perform Get_scope
  let get_file file = Effect.perform (Get_file file)

  let add_to_files filename trie globals file old_imports explicit =
    Effect.perform (Add_to_files (filename, { trie; globals; file; old_imports; explicit }))
end

(* Add the declarations of one "option" command to those of the current source.  Called when the command is executed; the prescan below has normally already recorded the same thing, and merging is idempotent, so declaring it twice is harmless. *)
let declare_option opts =
  let st = Loading.get () in
  if st.started then fatal Option_not_at_start;
  match Options.installed () with
  (* If the options have already been fixed -- by the prescan of this very source, by an earlier source, or by the command line -- then all we can do is check that this declaration agrees with them. *)
  | Some current -> (
      match Options.agree current opts with
      | Ok () -> ()
      | Error ds -> fatal (Conflicting_options (st.source, "the options already in force", ds)))
  | None -> (
      match Options.merge st.options opts with
      | Ok options -> Loading.modify (fun s -> { s with options })
      | Error ds -> fatal (Conflicting_options (st.source, "an earlier 'option' command in it", ds))
      )

(* Read the leading "option" commands of a source, without executing anything else, and return what they declare.

   This has to be a separate pass because the notations for the universes are named after the modes of the mode theory, so they can't be installed until the options are fixed; but the parser needs them for the very first command that isn't an "option", which is parsed before it is executed.  Parsing the "option" commands themselves needs no notations, so this pass can run with no type theory installed at all.

   Any error here is ignored: the real pass re-parses and re-executes these same commands, and will report it then with a proper location. *)
let prescan_options (source : Asai.Range.source) : Options.partial * bool =
  let opts = ref Options.empty in
  (* Whether there is anything after the option block. *)
  let more = ref false in
  ( Reporter.try_with ~fatal:(fun _ -> ()) @@ fun () ->
    let p, src = Parser.Command.Parse.start_parse source in
    let rec go p src =
      match Parser.Command.Parse.final p with
      | Bof _ ->
          let p, src = Parser.Command.Parse.restart_parse p src in
          go p src
      | Option { options; _ } ->
          (match Options.merge !opts options with
          | Ok o -> opts := o
          (* A conflict between two "option" commands in the same source is reported by the real pass. *)
          | Error _ -> ());
          let p, src = Parser.Command.Parse.restart_parse p src in
          go p src
      | Eof -> src
      (* Anything else ends the option block, and we abandon this parse. *)
      | _ ->
          more := true;
          src in
    match go p src with
    | _, `File ic -> In_channel.close ic
    | _, `String _ -> () );
  (!opts, !more)

(* Fix the type theory options, if they haven't been fixed already.  This happens just before the first command of a source that isn't an "option" command, so that the leading "option" commands of that source -- its "option block" -- have all been accumulated by then.

   A *file* specifies a total set of options: the absence of an "option parametric" command asserts higher observational type theory just as positively as its presence asserts parametricity, and the absence of an "option modal" command asserts the trivial mode theory.  So if a file is the first source to fix the options, its completed set becomes the options in force, and the command-line flags, which are only partial, must agree with it.  If the options have already been fixed, the file's completed set must agree with them exactly.

   A string executed with -e, or input entered interactively or in ProofGeneral, is not a complete artifact in the same way, so it specifies only a partial set: it is merged with the command-line flags rather than checked against them. *)
let fix_source_options ~(source : string) ~(total : bool) (declared : Options.partial) =
  let flags = Flags.read () in
  let conflict other ds = fatal (Conflicting_options (source, other, ds)) in
  match Options.installed () with
  | None ->
      let opts =
        if total then (
          let opts = Options.complete declared in
          (match Options.agree opts flags.cmdline with
          | Ok () -> ()
          | Error ds -> conflict "the command line" ds);
          opts)
        else
          match Options.merge flags.cmdline declared with
          | Ok p -> Options.complete p
          | Error ds -> conflict "the command line" ds in
      (match Options.validate ~discreteness:(Discrete.enabled ()) opts with
      | Ok () -> ()
      | Error msgs -> fatal (Invalid_options msgs));
      flags.install opts
  | Some current -> (
      (* The options are already in force, so all we can do is check that this source agrees with them.  A file has to agree on everything, since its silence is an assertion; other sources only on what they mention. *)
      let declared = if total then Options.to_partial (Options.complete declared) else declared in
      match Options.agree current declared with
      | Ok () -> ()
      | Error ds -> conflict "the options already in force" ds)

(* Fix the options of the current source from what it has declared so far.  Normally its whole option block has already been prescanned and fixed by its caller, before the source was given a file identifier; this is the fallback for interactive and ProofGeneral input. *)
let fix_options () =
  let st = Loading.get () in
  if not st.options_fixed then begin
    Loading.modify (fun s -> { s with options_fixed = true });
    fix_source_options ~source:st.source ~total:st.total st.options
  end

(* Interactive and ProofGeneral input arrives one command at a time, and doesn't go through load_file or load_string, so it needs its own hook for the "option" block at the top of the buffer being processed.  This must be called *before* each command is parsed, not merely before it is executed, because parsing the first command that isn't an "option" needs the notations for the universes, which are named after the modes of the mode theory.

   Like the command line, interactive input constrains only the options it mentions.  We fix the options as soon as a command arrives that isn't an "option" command; until then the theory stays open, so that editing and re-processing the option block at the top of a buffer works.  Retracting back past it, though, cannot un-install a theory: ProofGeneral has to restart Narya for that. *)
let interactive_options_source (source : Asai.Range.source) =
  if Options.installed () = None then begin
    let opts, more = prescan_options source in
    (match Options.merge (Loading.get ()).options opts with
    | Ok options -> Loading.modify (fun s -> { s with options })
    (* A conflict is reported when the command itself is executed. *)
    | Error _ -> ());
    if more then fix_options ()
  end

let interactive_options (content : string) =
  interactive_options_source (`String { title = Some "interactive input"; content })

(* Save all the definitions from a given loaded file to a compiled disk file, along with other data such as the type theory options, the imported files, and the (supplied) export namespace. *)
let marshal (file : File.t) (filename : FilePath.filename) (trie : Scope.trie) =
  if __COMPILE_VERSION__ > 0 then
    let ofile = FilePath.replace_extension filename "nyo" in
    try
      Out_channel.with_open_bin ofile @@ fun chan ->
      Marshal.to_channel chan __COMPILE_VERSION__ [];
      Options.marshal chan (Options.get ());
      Marshal.to_channel chan (Discrete.enabled ()) [];
      Marshal.to_channel chan file [];
      Marshal.to_channel chan (Loading.get ()).imports [];
      Global.to_channel_origin chan (File file) [];
      Parser.Scope.to_channel chan trie [];
      Marshal.to_channel chan (Loading.get ()).actions []
      (* Just emit a warning if we can't write the compiled version *)
    with Sys_error _ -> emit (Cant_write_compiled_file ofile)

(* Load a file from a compiled disk file, if possible.  Returns its export namespace, or None if loading from a compiled file failed. *)
let rec unmarshal (file : File.t) (lookup : FilePath.filename -> File.t)
    (filename : FilePath.filename) =
  let ofile = FilePath.replace_extension filename "nyo" in
  (* To load a compiled file, first of all both the compiled file and its source file must exist, and the compiled file must be not older than the source.  (If the source was reformatted at the time of compiling, they could be exactly the same age.) *)
  if
    FileUtil.test Is_file filename
    && FileUtil.test Is_file ofile
    && not (FileUtil.test (Is_older_than filename) ofile)
  then
    (* Now we can start loading things. *)
    In_channel.with_open_bin ofile @@ fun chan ->
    (* We check it was compiled with the same version as us. *)
    let old_version = (Marshal.from_channel chan : int) in
    if __COMPILE_VERSION__ > 0 && old_version = __COMPILE_VERSION__ then (
      (* We also check it was compiled with the same type theory options as us.  Note that these include the mode theory: a compiled file contains marshaled modalities whose representation is specific to the theory it was compiled under, so loading it under a different one would be unsound. *)
      let old_options = Options.unmarshal chan in
      let old_discreteness = (Marshal.from_channel chan : bool) in
      match
        if old_options = Options.get () && old_discreteness = Discrete.enabled () then Ok ()
        else
          Error
            (Options.to_string old_options
            ^ if old_discreteness then " -deprecated-discreteness" else "")
      with
      | Ok () ->
          let old_file = (Marshal.from_channel chan : File.t) in
          (* Now we make sure none of the files *it* imports (transitively) have been modified more recently than the compilation, and that they have all been compiled. *)
          let old_imports = (Marshal.from_channel chan : (File.t * FilePath.filename) Bwd.t) in
          if
            Bwd.for_all
              (fun (_, ifile) ->
                let oifile = FilePath.replace_extension filename "nyo" in
                FileUtil.test Is_file oifile
                && (not (FileUtil.test (Is_older_than ifile) oifile))
                && not (FileUtil.test (Is_newer_than ofile) ifile))
              old_imports
          then (
            (* If so, we load all those files (from their compiled versions, or make sure that they were already loaded) right away.  We don't need their returned namespaces, since we aren't typechecking our compiled file. *)
            Mbwd.miter
              (fun [ (_, ifile) ] ->
                let _ = load_file ifile false in
                ())
              [ old_imports ];
            (* We create a hashtable mapping the old files to new ones. *)
            let table = Hashtbl.create 20 in
            Mbwd.miter (fun [ (i, ifile) ] -> Hashtbl.add table i (lookup ifile)) [ old_imports ];
            Hashtbl.add table old_file file;
            let find_in_table x =
              Hashtbl.find_opt table x
              <|> Anomaly "missing file identifier while unmarshaling compiled file" in
            (* Now we load the definitions from the compiled file, replacing all the old files by the new ones. *)
            let unit_entry = Global.from_istream_origin find_in_table (Channel chan) (File file) in
            let trie = Parser.Scope.from_istream (Channel chan) find_in_table in
            (* We check whether the compiled file had any actions, and issue a warning if so *)
            if (Marshal.from_channel chan : bool) then emit (Actions_in_compiled_file ofile);
            Some (trie, unit_entry, old_imports))
          else None
      | Error flags ->
          emit (Incompatible_flags (filename, flags));
          None)
    else None
  else None

(* Load a file, possibly one specified on the command line, either from source or from a compiled version. *)
and load_file filename top =
  if not (FilePath.check_extension filename "ny") then fatal (Invalid_filename filename);
  (* We normalize the file path to a reduced absolute one, so we can use it for a hashtable key. *)
  let filename =
    if FilePath.is_relative filename then FilePath.make_absolute (Loading.get ()).cwd filename
    else filename in
  let filename = FilePath.reduce filename in
  match Loaded.get_file filename with
  | Some ({ trie; globals; file; old_imports; explicit = top' }, mtime) ->
      (* If we already loaded that file, first we check that neither it nor any of its imports have been modified more recently that when they were loaded. *)
      if (FileUtil.stat filename).modification_time > mtime then fatal (Library_modified filename);
      Bwd.iter
        (fun (_, f) ->
          if (FileUtil.stat filename).modification_time > mtime then fatal (Library_modified f))
        old_imports;
      (* We add it back into Global, and to the 'all' namespace if it wasn't already there. *)
      Global.add_file file globals;
      if top && not top' then (
        Loaded.add_to_scope trie;
        (* Ensure that it's marked as having been loaded explicitly. *)
        Loaded.add_to_files filename trie globals file old_imports true);
      (* We also add it to the list of things imported by the current ambient file.  TODO: Should that go in execute_command Import? *)
      Loading.modify (fun s -> { s with imports = Snoc (s.imports, (file, filename)) });
      (* Return its saved export namespace. *)
      trie
  | None ->
      (* Otherwise, we have to load it.  First we check for circular dependencies. *)
      (let parents = (Loading.get ()).parents in
       if Bwd.exists (fun x -> x = filename) parents then
         fatal (Circular_import (Bwd.to_list (Snoc (parents, filename)))));
      (* Read this file's option block and fix the type theory, before we give the file an identifier.  The identifier has to come afterwards because installing higher observational type theory allocates identifiers for its own bootstrap files, and the fibrancy data it unmarshals refers to constants by those identifiers without relinking them; so the bootstrap files must be the first ones created in any run that uses them. *)
      let source = Printf.sprintf "file '%s'" (FilePath.basename filename) in
      let file_options, _ = prescan_options (`File filename) in
      fix_source_options ~source ~total:true file_options;
      (* We make a name for it *)
      let file = File.make (`File filename) in
      (* Now we record it as a file that was imported by the current file. *)
      Loading.modify (fun s -> { s with imports = Snoc (s.imports, (file, filename)) });
      (* Then we load it, in its directory and with itself added to the list of parents. *)
      let rename i = (fst (Loaded.get_file i <|> Anomaly "missing file in load_file")).file in
      let trie, imports =
        Loading.run
          ~init:
            {
              cwd = FilePath.dirname filename;
              parents = Snoc ((Loading.get ()).parents, filename);
              imports = Emp;
              actions = false;
              source;
              options = file_options;
              options_fixed = true;
              started = false;
              (* A file specifies a total set of options; see fix_options. *)
              total = true;
            }
        @@ fun () ->
        (* If there's a compiled version, and we aren't in source-only mode, and this file wasn't specified explicitly on the command-line, we try loading the compiled version. *)
        let trie, globals, old_imports, which =
          let flags = Flags.read () in
          match
            if flags.source_only || List.mem filename flags.top_files then None
            else unmarshal file rename filename
          with
          | Some (trie, globals, old_imports) -> (trie, globals, old_imports, `Compiled)
          | None ->
              (* If we are in source-only mode, or this file was specified explicitly on the command-line, or if unmarshal failed (e.g. the compiled file is outdated), we load it from source. *)
              if not top then emit (Loading_file filename);
              (* If reformatting is enabled, and this file was explicitly specified on the command line, create a buffer to hold its reformatting. *)
              let buf =
                if (Flags.read ()).reformat && List.mem filename flags.top_files then
                  Some (Buffer.create 100)
                else None in
              let renderer = Option.map (PPrint.ToBuffer.pretty 1.0 (Display.columns ())) buf in
              (* Parse and execute the file and save its exported trie and global definitions *)
              let exported, unsolved =
                execute_source ~holes_allowed:top file ?renderer (`File filename) in
              (match buf with
              | None -> ()
              | Some buf -> (
                  (* If the reformatted version didn't change, do nothing. *)
                  let infile = open_in_bin filename in
                  let oldstr =
                    Fun.protect ~finally:(fun () -> close_in infile) @@ fun () ->
                    really_input_string infile (in_channel_length infile) in
                  if oldstr <> Buffer.contents buf then
                    try
                      (* Back up the original file to a new backup file name. *)
                      let bakfile, n = (filename ^ ".bak.", ref 0) in
                      while FileUtil.test Is_file (bakfile ^ string_of_int !n) do
                        n := !n + 1
                      done;
                      let bakfile = bakfile ^ string_of_int !n in
                      FileUtil.cp [ filename ] bakfile;
                      (* Overwrite the file with its reformatted version. *)
                      let outfile = open_out filename in
                      Fun.protect ~finally:(fun () -> close_out outfile) @@ fun () ->
                      output_string outfile (Buffer.contents buf)
                      (* Ignore file errors (e.g. read-only source file) *)
                    with Sys_error _ -> ()));
              (* Save the compiled version, if it contains no holes (holes contain a functional value). *)
              if unsolved = 0 then marshal file filename exported;
              (exported, Global.find_file file, (Loading.get ()).imports, `Source) in
        (* Then we add it to the table of loaded files and (possibly) the content of top-level files. *)
        if not top then emit (File_loaded (filename, which));
        Loaded.add_to_files filename trie globals file old_imports top;
        if top then Loaded.add_to_scope trie;
        (trie, (Loading.get ()).imports) in
      (* We add the files that it imports to those of the current file, since the imports list is supposed to be transitive. *)
      Loading.modify (fun s -> { s with imports = Bwd_extra.append s.imports imports });
      trie

(* Load an -e string or stdin. *)
and load_string ?init_visible title content =
  (* There is no caching and no change of state, since it can't be "required" from another file.  The caller specifies whether to use a special initial namespace. *)
  (* As in load_file, the option block is read and the type theory fixed before any file identifier is allocated.  Unlike a file, a string constrains only the options it mentions. *)
  let source = Printf.sprintf "the string '%s'" title in
  let str_options, _ = prescan_options (`String { title = Some title; content }) in
  (match Options.merge (Loading.get ()).options str_options with
  | Ok options -> Loading.modify (fun s -> { s with options })
  | Error ds -> fatal (Conflicting_options (source, "an earlier 'option' command", ds)));
  fix_options ();
  let file = File.make (`Other title) in
  let trie, _ =
    execute_source ~holes_allowed:true ?init_visible file (`String { title = Some title; content })
  in
  (* A string is always at top-level, so we always add it to 'all'. *)
  Loaded.add_to_scope trie;
  trie

(* Given a source (file or string), parse and execute all the commands in it, in a local scope that starts with either the supplied scope or a default one. *)
and execute_source ~holes_allowed ?init_visible ?renderer file (source : Asai.Range.source) =
  Origin.with_file ~holes_allowed file @@ fun () ->
  Option.iter Scope.set_visible init_visible;
  let p, src = Parser.Command.Parse.start_parse source in
  Reporter.try_with
    (fun () -> batch renderer p src `None [])
    ~fatal:(fun d ->
      match d.message with
      | Quit _ ->
          let src =
            match source with
            | `File name -> Some name
            | `String { title; _ } -> title in
          Reporter.emit (Quit src)
      | _ -> Reporter.fatal_diagnostic d);
  (* A source consisting only of "option" commands (or of nothing at all) still fixes the options, since its silence about the rest of them is an assertion just as much as its declarations are. *)
  fix_options ();
  (Scope.get_export (), Global.current_unsolved_holes ())

(* Parse, execute (if requested by Flags), and reformat (if requested by Flags) all the commands in a source. *)
and batch renderer p src cdns ws =
  match Parser.Command.Parse.final p with
  | Eof -> (
      match renderer with
      | Some render -> render (pp_ws `Cut ws)
      | None -> ())
  | Bof ws ->
      let p, src = Parser.Command.Parse.restart_parse p src in
      batch renderer p src `Bof ws
  | cmd ->
      let new_cdns = Parser.Command.condense cmd in
      (* We discard the offset and hole information, since this is not used in interactive mode. *)
      let _ = execute_command cmd in
      let ws =
        match renderer with
        | Some render ->
            let ws =
              if cdns = `Bof || (cdns <> `None && cdns = new_cdns) then
                Whitespace.normalize_no_blanks ws
              else Whitespace.normalize 2 ws in
            let space_before_starting_comment = if cdns = `Bof then Some 0 else None in
            let pcmd, wcmd = Parser.Command.pp_command cmd in
            render
              (pp_ws ?space_before_starting_comment (if cdns = `Bof then `None else `Cut) ws ^^ pcmd);
            wcmd
        | None -> [] in
      let p, src = Parser.Command.Parse.restart_parse p src in
      batch renderer p src new_cdns ws

(* Wrapper around Parser.Command.execute that passes it the correct callbacks.  Does NOT check flags or reformat.  An uncaught "Failure" from anywhere inside a command (e.g. an internal invariant checked with "failwith") is a bug, so we convert it here into an ordinary fatal Anomaly.  This way it is reported like any other bug, and the caller -- an interactive loop, or the loading of another input file -- can carry on afterwards, rather than the exception escaping all the way out to the handler in Top.run_top and killing the whole session. *)
and execute_command cmd =
  let action_taken () = Loading.modify (fun s -> { s with actions = true }) in
  let get_file file = load_file file false in
  (* Anything that isn't an "option" command ends the source's option block and fixes the type theory.  Normally the prescan has already done that, but interactive and ProofGeneral input doesn't go through it. *)
  (match cmd with
  | Option _ -> ()
  | _ ->
      fix_options ();
      Loading.modify (fun s -> { s with started = true }));
  try Parser.Command.execute ~action_taken ~get_file ~declare_option cmd
  with Failure str -> fatal (Anomaly ("failure: " ^ str))
