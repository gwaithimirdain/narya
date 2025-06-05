open Bwd
open Util
open Core
open Reporter
module Trie = Yuujinchou.Trie

(* Parameter module for Yuujinchou *)
module Param = struct
  type data =
    [ `Constant of Constant.t | `Notation of User.prenotation * User.notation ]
    * Asai.Range.t option

  (* Currently we have no nontrivial tags, hooks, or contexts. *)
  type tag = unit
  type hook = unit
  type context = unit
end

(* Modifier module for Yuujinchou *)
module Mod = struct
  include Yuujinchou.Modifier.Make (Param)

  (* We wrap the 'union' operations of Yuujinchou.Trie so that they merge by performing the modifier shadow effect, just as Scope does.  This is in the development version of Yuujinchou but hasn't been released yet. *)
  let union ?prefix ?context t1 t2 = Trie.union ?prefix (Perform.shadow context) t1 t2

  let union_subtree ?prefix ?context t1 pt2 =
    Trie.union_subtree ?prefix (Perform.shadow context) t1 pt2

  let union_singleton ?prefix ?context t1 (path, data) =
    Trie.union_singleton ?prefix (Perform.shadow context) t1 (path, data)

  let union_root ?prefix ?context t r = Trie.union_root ?prefix (Perform.shadow context) t r
end

let () =
  Mod.register_printer (function
    | `NotFound _ -> Some "unhandled Modifier.not_found effect"
    | `Shadow _ -> Some "unhandled Modifier.shadow effect"
    | `Hook _ -> Some "unhandled Modifier.hook effect")

module M = Algaeff.Mutex.Make ()

exception Locked = M.Locked

(* Scope state: a visible namespace, an export namespace, an export prefix, a notation situation, and a set of configuration options. *)
type trie = (Param.data, Param.tag) Trie.t

type scope = {
  (* The 'visible' namespace is the names that can be used in the present file/section. *)
  visible : trie;
  (* The 'export' namespace is the names that will appear in the outer file/section once this one is closed, not yet prefixed with the current section name. *)
  export : trie;
  (* The prefix that will be prepended to all exported names when they are exported.  This is just the "immediate" prefix of the current section, not including any outer enclosing sections. *)
  prefix : Trie.bwd_path;
  (* The notation situation that applies in the present file/section. *)
  situation : Situation.t;
  options : Options.t;
}

(* A Scope.t has an inner scope (the current file/section) and also maintains a stack of outer scopes. *)
type t = { outer : scope Bwd.t; inner : scope }

(* This is a function taking a unit argument, rather than a constant, so it doesn't try to access builtins before they're set. *)
let empty () : t =
  {
    outer = Emp;
    inner =
      {
        visible = Trie.empty;
        export = Trie.empty;
        prefix = Emp;
        situation = !Situation.builtins;
        options = Options.default;
      };
  }

module S = State.Make (struct
  type nonrec t = t
end)

let () =
  S.register_printer (function
    | `Get -> Some "unhandled Scope.get effect"
    | `Set _ -> Some "unhandled Scope.set effect")

module Situation = struct
  include Situation

  let get () = M.exclusively @@ fun () -> (S.get ()).inner.situation

  let modify f =
    M.exclusively @@ fun () ->
    let s = S.get () in
    let x, situation = f s.inner.situation in
    S.set { s with inner = { s.inner with situation } };
    x

  let left_closeds : unit -> (No.plus_omega, No.strict) Notation.entry =
   fun () ->
    let s = get () in
    (Situation.EntryMap.find_opt No.plus_omega s.tighters <|> Anomaly "missing left_closeds").strict

  let tighters : type strict tight. (tight, strict) No.iinterval -> (tight, strict) Notation.entry =
   fun { strictness; endpoint } ->
    let ep = Situation.EntryMap.find_opt endpoint (get ()).tighters <|> Anomaly "missing tighters" in
    match strictness with
    | Nonstrict -> ep.nonstrict
    | Strict -> ep.strict

  let left_opens : Token.t -> No.interval option =
   fun tok -> Notation.TokMap.find_opt tok (get ()).left_opens

  let unparse : Situation.PrintKey.t -> User.notation option =
   fun c -> Situation.PrintMap.find_opt c (get ()).unparse

  let add_users_to : Situation.t -> trie -> Situation.t =
   fun sit trie ->
    Seq.fold_left
      (fun state (_, ((data, _), _)) ->
        match data with
        | `Notation (user, _) -> snd (Situation.add_user_to user state)
        | _ -> state)
      sit
      (Trie.to_seq (Trie.find_subtree [ "notations" ] trie))

  (* These are used only internally and for whitebox testing.  Once the whitebox tests are converted to blackbox ones, we can remove them from the interface. *)

  let add : type left tight right. (left, tight, right) Notation.notation -> unit =
   fun notn -> modify @@ fun s -> ((), Situation.add notn s)

  let add_user : User.prenotation -> User.notation * User.key list =
   fun user -> modify @@ fun s -> Situation.add_user_to user s
end

let export_prefix () = (S.get ()).inner.prefix

(* The following operations are copied from Yuujinchou.Scope, but acting only on the inner scope. *)

let resolve p = M.exclusively @@ fun () -> Trie.find_singleton p (S.get ()).inner.visible
let resolve_export p = M.exclusively @@ fun () -> Trie.find_singleton p (S.get ()).inner.export

(* Does not modify the notation situation.  This is dangerous, so we don't export it. *)
let _modify_visible ?context_visible m =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      { s.inner with visible = Mod.modify ?context:context_visible ~prefix:Emp m s.inner.visible };
  }

let modify_options f =
  M.exclusively @@ fun () ->
  S.modify @@ fun s -> { s with inner = { s.inner with options = f s.inner.options } }

let modify_export ?context_export m =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      {
        s.inner with
        export = Mod.modify ?context:context_export ~prefix:(export_prefix ()) m s.inner.export;
      };
  }

(* Copy the visible namespace into the export namespace. *)
let export_visible ?context_modifier ?context_export m =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      {
        s.inner with
        export =
          Mod.union ?context:context_export ~prefix:(export_prefix ()) s.inner.export
          @@ Mod.modify ?context:context_modifier m s.inner.visible;
      };
  }

(* Add a name to the visible and export namespaces.  Does not modify the notation situation -- this is dangerous, so we don't export it; instead use 'define' and 'define_notation'. *)
let include_singleton ?context_visible ?context_export (path, x) =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      {
        s.inner with
        visible = Mod.union_singleton ?context:context_visible s.inner.visible (path, x);
        (* I don't know what the ~prefix argument to union_singleton does, but it *doesn't* prepend that prefix to the names being added. *)
        export =
          Mod.union_singleton ?context:context_export ~prefix:(export_prefix ()) s.inner.export
            (path, x);
      };
  }

(* Create a new Constant.t and define a name to equal it. *)
let define compunit ?loc name =
  let c = Constant.make compunit in
  include_singleton (name, ((`Constant c, loc), ()));
  c

(* Install a user notation and define a name to equal it.  Returns a list of the old notations shadowed by this one. *)
let define_notation user ?loc name =
  let notn, shadow = Situation.add_user user in
  include_singleton (name, ((`Notation (user, notn), loc), ()));
  shadow

(* As above, but only adding it to the visible namespace and not the export one.  Also does not modify the notation situation; this is dangerous, so we don't export it. *)
let _import_singleton ?context_visible (path, x) =
  M.exclusively @@ fun () ->
  S.modify @@ fun s ->
  {
    s with
    inner =
      {
        s.inner with
        visible = Mod.union_singleton ?context:context_visible s.inner.visible (path, x);
      };
  }

(* Include a subtree into the visible namespace at a specified location.  Also adds notations from the subtree "notations" namespace into the notation situation IF the supplied path is empty (since then this is getting merged into the ambient "notations" namespace).  Adds the subtree into the export namespace if "export" is true.  This is not wrapped in the mutex, hence not exported. *)
let unsafe_include_subtree ?context_modifier ?context_visible ?context_export
    ?(modifier = Yuujinchou.Language.id) ~export (path, ns) =
  S.modify @@ fun s ->
  let ns = Mod.modify ?context:context_modifier ~prefix:Emp modifier ns in
  let situation =
    if List.is_empty path then Situation.add_users_to s.inner.situation ns else s.inner.situation
  in
  let export =
    if export then
      Mod.union_subtree ?context:context_export ~prefix:(export_prefix ()) s.inner.export (path, ns)
    else s.inner.export in
  {
    s with
    inner =
      {
        s.inner with
        visible = Mod.union_subtree ?context:context_visible s.inner.visible (path, ns);
        export;
        situation;
      };
  }

(* Same, but wrapped in the mutex, and always add it to the export. *)
let include_subtree ?context_modifier ?context_visible ?context_export ?modifier (path, ns) =
  M.exclusively @@ fun () ->
  unsafe_include_subtree ?context_modifier ?context_visible ?context_export ?modifier ~export:true
    (path, ns)

(* Same, but only add it to the visible and not the export namespace. *)
let import_subtree ?context_modifier ?context_visible ?modifier (path, ns) =
  M.exclusively @@ fun () ->
  unsafe_include_subtree ?context_modifier ?context_visible ?modifier ~export:false (path, ns)

let get_visible () = M.exclusively @@ fun () -> (S.get ()).inner.visible
let get_export () = M.exclusively @@ fun () -> (S.get ()).inner.export
let get_options () = M.exclusively @@ fun () -> (S.get ()).inner.options

(* Set the visible namespace, e.g. before going into interactive mode.  Also set the notation situation to consist of the user notations from that namespace. *)
let set_visible visible =
  M.exclusively @@ fun () ->
  let situation = Situation.add_users_to !Situation.builtins visible in
  S.modify (fun s -> { s with inner = { s.inner with visible; situation } })

(* Start a new section, with specified prefix.  Keeps the ambient visible namespace, but starts with empty export namespace which will collect only the names defined in the section.  *)
let start_section prefix =
  if List.mem "notations" prefix then fatal (Invalid_section_name prefix);
  M.exclusively @@ fun () ->
  S.modify (fun s ->
      let new_scope : scope =
        {
          visible = s.inner.visible;
          export = Trie.empty;
          prefix = Bwd.of_list prefix;
          situation = s.inner.situation;
          options = s.inner.options;
        } in
      { outer = Snoc (s.outer, s.inner); inner = new_scope })

(* How many nested sections are we inside? *)
let count_sections () = M.exclusively @@ fun () -> Bwd.length (S.get ()).outer

(* Finish a section, integrating its exported names into the previous section's namespaces (import and export) with the prefix attached.  Doesn't add notations to the situation since the prefix is (presumably) nonempty.  Returns the prefix that was used. *)
let end_section () =
  M.exclusively @@ fun () ->
  let ending_scope = (S.get ()).inner in
  try
    S.modify (fun s ->
        match s.outer with
        | Snoc (outer, inner) -> { outer; inner }
        | Emp -> raise (Failure "no section here to end"));
    unsafe_include_subtree ~export:true (Bwd.to_list ending_scope.prefix, ending_scope.export);
    Some (Bwd.to_list ending_scope.prefix)
  with Failure _ -> None

(* We remove the Mod.run from Scope.run and let the caller control it separately.  Also sets the notation situation.  Note that this *overrides* (dynamically, locally) any "actual" namespace and notations in the outer state.  It is used for loading files and strings, which are atomic undo units, and for "going back in time" temporarily to solve an old hole. *)
let run ?(export_prefix = Emp) ?(init_visible = Trie.empty) ?init_situation
    ?(options = Options.default) f =
  let situation =
    match init_situation with
    | Some s -> s
    | None -> Situation.add_users_to !Situation.builtins init_visible in
  let init =
    {
      outer = Emp;
      inner =
        { visible = init_visible; export = Trie.empty; prefix = export_prefix; situation; options };
    } in
  M.run @@ fun () -> S.run ~init f

(* Like 'run', but override the handlers for the scope state effects instead of running a state module; hence no init_visible is given.  Unlike most RedPRL try_with functions, this one isn't designed for calling *inside* of an outer "run" to override some things locally, instead it is for *replacing* "run" by passing out the state effects to our History module.  Hence why it starts a new Mutex as well, and why we call it "run_with" instead of "try_with". *)
let run_with ?get ?set f = M.run @@ fun () -> S.try_with ?get ?set f

(* Look up a name to get a constant. *)
let lookup name =
  match resolve name with
  | Some ((`Constant c, _), ()) -> Some c
  | Some ((`Notation _, _), ()) -> None
  | None -> None

(* Backwards lookup of a constant to find its name. *)
let find_data trie x =
  Seq.find_map
    (fun (path, ((data, _), _)) -> if data = x then Some path else None)
    (Trie.to_seq trie)

let name_of c =
  match find_data (get_visible ()) (`Constant c) with
  | Some name -> name
  (* TODO: Better to munge the original name. *)
  | None -> [ "_UNNAMED_CONSTANT" ]

(* Check whether a new name will shadow something else in the export namespace, and warn if so. *)
let check_name name loc =
  match resolve_export name with
  | Some ((_, oldloc), ()) ->
      let extra_remarks =
        match oldloc with
        | Some loc -> [ Asai.Diagnostic.loctext ~loc "previous definition" ]
        | None -> [] in
      emit ?loc ~extra_remarks (Redefining_constant name)
  | None -> ()
