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

(* The modification time of a file.  We follow symlinks, since a file loaded through a symlink is modified when its target is.  (The tests in FileUtil.test, such as Is_older_than, compare against the modification time of a symlink itself.) *)
let mtime file = (FileUtil.stat ~dereference:true file).modification_time

(* Normalize a file path, relative to a given directory, to a reduced absolute one, so we can use it as a hashtable key.  Symlinks are not resolved: a file loaded through a symlink is identified by the path of the symlink, has its compiled version stored next to the symlink, and resolves its imports relative to the symlink's directory.  Consistently with this, ".." is reduced lexically, so that "a/c/../b.ny" is the same file as "a/b.ny" even if "a/c" is a symlink. *)
let normalize_filename cwd filename =
  let filename =
    if FilePath.is_relative filename then FilePath.make_absolute cwd filename else filename in
  FilePath.reduce ~no_symlink:true filename

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
    (* Marshal all the command-line type theory flags to disk. *)
    marshal : Out_channel.t -> unit;
    (* Unmarshal all the command-line type theory flags from a disk file and check that they agree with the current ones, returning the unmarshaled ones if not. *)
    unmarshal : Istream.t -> (unit, string) Result.t;
    (* Load files from source only (not compiled versions). *)
    source_only : bool;
    (* Don't write compiled versions of files to disk. *)
    no_write_compiled : bool;
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
        Hashtbl.add loaded_files file (data, mtime file);
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

(* Written after all the marshaled values in a compiled file, so that we can tell whether a compiled file is complete before we start loading it. *)
let compiled_trailer = "\nend of narya compiled file\n"

(* Create a new temporary file in the same directory as a given file, so that it can be renamed onto that file.  Unlike Filename.temp_file, we create it with the ordinary permissions (subject to the umask), since it will become the compiled file. *)
let open_temp_file ofile =
  let rng = Random.State.make_self_init () in
  let rec go n =
    let tmpfile = Printf.sprintf "%s.%06x.tmp" ofile (Random.State.bits rng land 0xFFFFFF) in
    match
      Out_channel.open_gen [ Open_wronly; Open_creat; Open_excl; Open_binary ] 0o666 tmpfile
    with
    | chan -> (tmpfile, chan)
    (* If the name was taken, try another one. *)
    | exception (Sys_error _ as e) ->
        if n < 100 && Sys.file_exists tmpfile then go (n + 1) else raise e in
  go 0

(* Save all the definitions from a given loaded file to a compiled disk file, along with other data such as the command-line type theory flags, the imported files, and the (supplied) export namespace.  We write to a temporary file and then rename it onto the compiled file, so that another run never sees a partially written compiled file, and an interrupted run doesn't leave one behind. *)
let marshal (file : File.t) (filename : FilePath.filename) (trie : Scope.trie) =
  if __COMPILE_VERSION__ > 0 && not (Flags.read ()).no_write_compiled then
    let ofile = FilePath.replace_extension filename "nyo" in
    try
      let tmpfile, chan = open_temp_file ofile in
      try
        (try
           Marshal.to_channel chan __COMPILE_VERSION__ [];
           (Flags.read ()).marshal chan;
           Marshal.to_channel chan file [];
           Marshal.to_channel chan (Loading.get ()).imports [];
           Global.to_channel_origin chan (File file) [];
           Parser.Scope.to_channel chan trie [];
           Marshal.to_channel chan (Loading.get ()).actions [];
           Out_channel.output_string chan compiled_trailer;
           (* Closing flushes the channel, which can also fail. *)
           Out_channel.close chan
         with e ->
           Out_channel.close_noerr chan;
           raise e);
        Sys.rename tmpfile ofile
      with e ->
        (try Sys.remove tmpfile with Sys_error _ -> ());
        raise e
      (* Just emit a warning if we can't write the compiled version *)
    with Sys_error _ -> emit (Cant_write_compiled_file ofile)

(* Load a file from a compiled disk file, if possible.  Returns its export namespace, or None if loading from a compiled file failed. *)
let rec unmarshal (file : File.t) (lookup : FilePath.filename -> File.t)
    (filename : FilePath.filename) =
  let ofile = FilePath.replace_extension filename "nyo" in
  (* To load a compiled file, first of all both the compiled file and its source file must exist, and the compiled file must be not older than the source.  (If the source was reformatted at the time of compiling, they could be exactly the same age.) *)
  if FileUtil.test Is_file filename && FileUtil.test Is_file ofile && mtime ofile >= mtime filename
  then
    (* We read the whole compiled file into memory, and check that it is complete (it could have been truncated, e.g. by an older version of Narya that didn't write compiled files atomically), before unmarshaling anything from it.  Otherwise we could fail partway through after having already modified the global state.  If it isn't complete, we treat it like an outdated compiled file and load the source instead. *)
    match
      Option.bind
        (try Some (In_channel.with_open_bin ofile In_channel.input_all) with Sys_error _ -> None)
        (Istream.framed_string ~trailer:compiled_trailer)
    with
    | None -> None
    | Some chan ->
        (* We check it was compiled with the same version as us. *)
        let old_version = (Istream.unmarshal chan : int) in
        if __COMPILE_VERSION__ > 0 && old_version = __COMPILE_VERSION__ then (
          (* We also check it was compiled with the same type theory flags as us. *)
          match (Flags.read ()).unmarshal chan with
          | Ok () ->
              let old_file = (Istream.unmarshal chan : File.t) in
              (* Now we make sure none of the files *it* imports (transitively) have been modified more recently than the compilation, and that they have all been compiled. *)
              let old_imports = (Istream.unmarshal chan : (File.t * FilePath.filename) Bwd.t) in
              if
                Bwd.for_all
                  (fun (_, ifile) ->
                    let oifile = FilePath.replace_extension ifile "nyo" in
                    FileUtil.test Is_file oifile
                    && mtime oifile >= mtime ifile
                    && mtime ifile <= mtime ofile)
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
                Mbwd.miter
                  (fun [ (i, ifile) ] -> Hashtbl.add table i (lookup ifile))
                  [ old_imports ];
                Hashtbl.add table old_file file;
                let find_in_table x =
                  Hashtbl.find_opt table x
                  <|> Anomaly "missing file identifier while unmarshaling compiled file" in
                (* Now we load the definitions from the compiled file, replacing all the old files by the new ones. *)
                let unit_entry = Global.from_istream_origin find_in_table chan (File file) in
                let trie = Parser.Scope.from_istream chan find_in_table in
                (* We check whether the compiled file had any actions, and issue a warning if so *)
                if (Istream.unmarshal chan : bool) then emit (Actions_in_compiled_file ofile);
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
  let filename = normalize_filename (Loading.get ()).cwd filename in
  match Loaded.get_file filename with
  | Some ({ trie; globals; file; old_imports; explicit = top' }, loaded_mtime) ->
      (* If we already loaded that file, first we check that neither it nor any of its imports have been modified more recently that when they were loaded.  Each file is compared against its own loading time; an import is quite normally newer than the file that imports it. *)
      if mtime filename > loaded_mtime then fatal (Library_modified filename);
      Bwd.iter
        (fun (_, f) ->
          match Loaded.get_file f with
          | Some (_, fmtime) -> if mtime f > fmtime then fatal (Library_modified f)
          | None -> ())
        old_imports;
      (* We add it back into Global, and to the 'all' namespace if it wasn't already there. *)
      Global.add_file file globals;
      if top && not top' then (
        Loaded.add_to_scope trie;
        (* Ensure that it's marked as having been loaded explicitly. *)
        Loaded.add_to_files filename trie globals file old_imports true);
      (* We also add it, and the files it imports, to the list of things imported by the current ambient file, since that list is supposed to be transitive.  (The other branch appends the same thing, in the same order, after loading the file.)  TODO: Should that go in execute_command Import? *)
      Loading.modify (fun s ->
          { s with imports = Bwd_extra.append (Snoc (s.imports, (file, filename))) old_imports });
      (* Return its saved export namespace. *)
      trie
  | None ->
      (* Otherwise, we have to load it.  First we check for circular dependencies. *)
      (let parents = (Loading.get ()).parents in
       if Bwd.exists (fun x -> x = filename) parents then
         fatal (Circular_import (Bwd.to_list (Snoc (parents, filename)))));
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
      if
        Reporter.accumulates
          (function
            | Quit _ -> true
            | _ -> false)
          d
      then
        let src =
          match source with
          | `File name -> Some name
          | `String { title; _ } -> title in
        Reporter.emit (Quit src)
      else Reporter.fatal_diagnostic d);
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
  try Parser.Command.execute ~action_taken ~get_file cmd
  with Failure str -> fatal (Anomaly ("failure: " ^ str))
