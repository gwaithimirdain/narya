open Bwd
open Core
open Top

(* A file that was loaded earlier is checked, when it comes up again, to make sure that neither it
   nor anything it imports has changed on disk since it was loaded; each file is compared against
   its own loading time, since an import is quite normally *older* or *newer* than the file that
   imports it without either of them having changed.  Only the importing file can be modified
   between two runs of Narya, so a cram test can exercise the "hasn't changed" side of this but not
   the other; here we load a file, modify the file it imports as an editor would during a session,
   and load it again. *)

let write name contents =
  Out_channel.with_open_text name (fun chan -> Out_channel.output_string chan contents)

let () =
  let dir = Filename.temp_file "narya-library-modified" "" in
  Sys.remove dir;
  Sys.mkdir dir 0o700;
  Sys.chdir dir;
  write "lib.ny" "axiom A : Type\n";
  write "user.ny" "import \"lib\"\naxiom a : A\n";
  inputs := Snoc (Emp, `File "user.ny");
  hott := false;
  let modified = ref false in
  (try
     run_top ~use_ansi:false ~install_hott:(fun () -> ()) @@ fun () ->
     (* Someone edits the imported file while we are running. *)
     let later = Unix.gettimeofday () +. 10. in
     Unix.utimes "lib.ny" later later;
     Reporter.try_with
       ~fatal:(fun d ->
         match d.message with
         | Library_modified _ -> modified := true
         | _ -> Reporter.display ~output:stderr d)
       (fun () -> ignore (Execute.load_file "user.ny" false))
   with Top.Exit -> ());
  if not !modified then (
    print_endline "expected 'library modified' for an import that changed since it was loaded";
    exit 1)
