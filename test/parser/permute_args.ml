open Util
open Parser
open Notation
open Testutil
open Repl

let () =
  run @@ fun () ->
  assume "A" "Type";
  assume "foo" "A → A → A";
  let foo = Option.get (Scope.lookup [ "foo" ]) in
  let _ =
    Scope.Situation.add_user
      (User
         {
           id = User.Id.make ();
           name = "amp";
           fixity = Infix No.zero;
           pattern = Var ((Plain "x", `Nobreak, []), Var_nil ((Op "&", `Break, []), (Plain "y", [])));
           key = `Constant foo;
           val_args = [ Arg "y"; Arg "x" ];
         }) in
  assume "a" "A";
  assume "b" "A";
  equal_at "foo a b" "b & a" "A";
  print "b & a";
  ()
