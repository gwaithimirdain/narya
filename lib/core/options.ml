(* The "options" of a Narya session are the flags that determine its type theory: parametricity and its arity and direction, internal vs. external, and the mode theory together with any renaming of its modes, modalities, and cells.  These are distinguished from the *display* options (see Display), which only affect how output is printed and can be changed at any time with a "display" command, and from the *execution* options (like -source-only and the list of input files), which are properties of an invocation rather than of the code.

   Because the internal design doesn't allow the type theory to change partway through a run, the options must be fixed before any code is checked.  They can be specified in three ways: by command-line flags, by "option" commands at the beginning of a source file, or by defaulting.  A *source file* is regarded as specifying a *total* set of options: the absence of an "option parametric" command asserts higher observational type theory just as positively as its presence asserts parametricity, and the absence of an "option modal" command asserts the trivial mode theory.  The command line, by contrast, and strings executed with -e or entered interactively, specify only a *partial* set: they constrain the fields they mention and say nothing about the others.  All the specifications encountered in a single run must agree.

   Thus a file is self-describing: running "narya foo.ny" uses the theory that foo.ny declares, and loading foo.ny from another file, or editing it in ProofGeneral, uses that same theory.  Command-line flags remain available, but when any file is loaded they can only agree with it or conflict with it. *)

module Theories = Modal.Theories

(* A complete specification of a type theory. *)
type t = {
  (* Whether we are doing higher observational type theory (fibrancy) rather than parametricity. *)
  hott : bool;
  arity : int;
  refl_char : char;
  refl_names : string list;
  internal : bool;
  theory : Theories.name;
  (* Renamings of the modes, modalities, and modal cells of the mode theory.  Empty means "leave them all at their defaults"; renaming is all-or-nothing per kind. *)
  modes : string list;
  modalities : string list;
  modalcells : string list;
}

let defaults =
  {
    hott = true;
    arity = 2;
    refl_char = 'e';
    refl_names = [ "refl"; "Id"; "ap" ];
    internal = true;
    theory = Theories.trivial;
    modes = [];
    modalities = [];
    modalcells = [];
  }

(* A partial specification, in which each field may be left unspecified. *)
type partial = {
  phott : bool option;
  parity : int option;
  prefl_char : char option;
  prefl_names : string list option;
  pinternal : bool option;
  ptheory : Theories.name option;
  pmodes : string list option;
  pmodalities : string list option;
  pmodalcells : string list option;
}

let empty =
  {
    phott = None;
    parity = None;
    prefl_char = None;
    prefl_names = None;
    pinternal = None;
    ptheory = None;
    pmodes = None;
    pmodalities = None;
    pmodalcells = None;
  }

let is_empty p = p = empty

(* Fill in the unspecified fields of a partial specification with the defaults, producing a total one. *)
let complete (p : partial) : t =
  {
    hott = Option.value ~default:defaults.hott p.phott;
    arity = Option.value ~default:defaults.arity p.parity;
    refl_char = Option.value ~default:defaults.refl_char p.prefl_char;
    refl_names = Option.value ~default:defaults.refl_names p.prefl_names;
    internal = Option.value ~default:defaults.internal p.pinternal;
    theory = Option.value ~default:defaults.theory p.ptheory;
    modes = Option.value ~default:defaults.modes p.pmodes;
    modalities = Option.value ~default:defaults.modalities p.pmodalities;
    modalcells = Option.value ~default:defaults.modalcells p.pmodalcells;
  }

(* Descriptions of the individual fields, for reporting disagreements.  Each entry gives the name of the field, how to display one of its values, how to extract it from a total specification, and how to extract it from a partial one. *)
type field = Field : string * ('a -> string) * (t -> 'a) * (partial -> 'a option) -> field

let show_parametric b = if b then "higher observational type theory" else "parametricity"
let show_int = string_of_int
let show_char c = String.make 1 c
let show_names xs = if xs = [] then "(none)" else String.concat "," xs
let show_internal b = if b then "internal" else "external"

let fields =
  [
    Field ("theory", show_parametric, (fun t -> t.hott), fun p -> p.phott);
    Field ("arity", show_int, (fun t -> t.arity), fun p -> p.parity);
    Field ("direction letter", show_char, (fun t -> t.refl_char), fun p -> p.prefl_char);
    Field ("reflexivity names", show_names, (fun t -> t.refl_names), fun p -> p.prefl_names);
    Field ("parametricity", show_internal, (fun t -> t.internal), fun p -> p.pinternal);
    Field ("mode theory", Theories.to_string, (fun t -> t.theory), fun p -> p.ptheory);
    Field ("mode names", show_names, (fun t -> t.modes), fun p -> p.pmodes);
    Field ("modality names", show_names, (fun t -> t.modalities), fun p -> p.pmodalities);
    Field ("modal cell names", show_names, (fun t -> t.modalcells), fun p -> p.pmodalcells);
  ]

(* The ways in which a partial specification disagrees with a total one.  Each disagreement names the field and both values.  An empty list means they agree. *)
let disagreements (t : t) (p : partial) : string list =
  List.filter_map
    (fun (Field (name, show, get, pget)) ->
      match pget p with
      | Some v when v <> get t ->
          Some (Printf.sprintf "%s (%s vs. %s)" name (show v) (show (get t)))
      | _ -> None)
    fields

(* A total specification, viewed as a partial one that happens to specify every field.  Used to compare two total specifications for agreement. *)
let to_partial (t : t) : partial =
  {
    phott = Some t.hott;
    parity = Some t.arity;
    prefl_char = Some t.refl_char;
    prefl_names = Some t.refl_names;
    pinternal = Some t.internal;
    ptheory = Some t.theory;
    pmodes = Some t.modes;
    pmodalities = Some t.modalities;
    pmodalcells = Some t.modalcells;
  }

let agree (t : t) (p : partial) : (unit, string list) result =
  match disagreements t p with
  | [] -> Ok ()
  | ds -> Error ds

(* The union of two partial specifications, with the second taking precedence.  Only meaningful when they don't disagree, which [merge] checks. *)
let union (p1 : partial) (p2 : partial) : partial =
  let pick a b = if b = None then a else b in
  {
    phott = pick p1.phott p2.phott;
    parity = pick p1.parity p2.parity;
    prefl_char = pick p1.prefl_char p2.prefl_char;
    prefl_names = pick p1.prefl_names p2.prefl_names;
    pinternal = pick p1.pinternal p2.pinternal;
    ptheory = pick p1.ptheory p2.ptheory;
    pmodes = pick p1.pmodes p2.pmodes;
    pmodalities = pick p1.pmodalities p2.pmodalities;
    pmodalcells = pick p1.pmodalcells p2.pmodalcells;
  }

(* Merge two partial specifications, failing if they specify different values for the same field.  Only fields specified by *both* can disagree: a field where one is silent is simply taken from the other, since neither is asserting anything about it. *)
let merge (p1 : partial) (p2 : partial) : (partial, string list) result =
  match
    List.filter_map
      (fun (Field (name, show, _, pget)) ->
        match (pget p1, pget p2) with
        | Some v1, Some v2 when v1 <> v2 ->
            Some (Printf.sprintf "%s (%s vs. %s)" name (show v1) (show v2))
        | _ -> None)
      fields
  with
  | [] -> Ok (union p1 p2)
  | ds -> Error ds

(* Check that a complete specification is internally consistent.  These are the checks that were previously performed by replaying the mutable references set by the command-line flag handlers, which made the resulting error messages depend on the order in which the flags happened to be written.  Here the whole specification is checked at once. *)
let validate ~(discreteness : bool) (t : t) : (unit, string list) result =
  let errors = ref [] in
  let err fmt = Printf.ksprintf (fun s -> errors := s :: !errors) fmt in
  let entry =
    match Theories.find t.theory with
    | Some e -> Some e
    | None ->
        err "unknown mode theory '%s'" (Theories.to_string t.theory);
        None in
  if t.arity < 0 || t.arity > 9 then err "arity %d is outside the supported range [0,9]" t.arity;
  if t.hott then begin
    if t.arity <> 2 then err "higher observational type theory requires arity 2";
    if not t.internal then err "external parametricity requires 'option parametric'";
    if discreteness then err "-deprecated-discreteness requires 'option parametric'"
  end;
  if discreteness && t.arity > 1 then err "discreteness with arity > 1 is not implemented";
  Option.iter
    (fun (e : Theories.entry) ->
      if e.requires_parametric && t.hott then
        err "the %s mode theory requires 'option parametric'" (Theories.to_string t.theory);
      (if not t.internal then
         match (e.external_ok, t.arity) with
         | `None, _ ->
             err "external parametricity requires a compatible mode theory, not %s"
               (Theories.to_string t.theory)
         | `One, 1 | `Any, _ -> ()
         | `One, _ ->
             err "the %s mode theory with external parametricity requires arity 1"
               (Theories.to_string t.theory));
      match (e.arity_ok, t.arity) with
      | `One, 1 | `Any, _ -> ()
      | `One, _ -> err "the %s mode theory requires arity 1" (Theories.to_string t.theory))
    entry;
  match List.rev !errors with
  | [] -> Ok ()
  | errs -> Error errs

(* Display a complete specification as the equivalent sequence of command-line flags, for error messages about compiled files. *)
let to_string (t : t) =
  String.concat " "
    (List.filter
       (fun s -> s <> "")
       [
         (if t.hott then "" else "-parametric");
         Printf.sprintf "-arity %d" t.arity;
         Printf.sprintf "-direction %s"
           (String.concat "," (String.make 1 t.refl_char :: t.refl_names));
         (if t.internal then "-internal" else "-external");
         (if t.theory = Theories.trivial then ""
          else
            match Theories.find t.theory with
            | Some e -> "-" ^ e.flag
            | None -> "-" ^ Theories.to_string t.theory);
         (if t.modes = [] then "" else "-modes " ^ String.concat "," t.modes);
         (if t.modalities = [] then "" else "-modalities " ^ String.concat "," t.modalities);
         (if t.modalcells = [] then "" else "-modalcells " ^ String.concat "," t.modalcells);
       ])

(* Note that the deprecated strict parametric discreteness is deliberately *not* one of these options.  It is set only by the command-line flag -deprecated-discreteness, and doesn't participate in the agreement check, so that a library can still be loaded both with and without it while old code is being ported.  It is recorded separately in compiled files; see Execute.marshal. *)

(* Marshaling, for recording in compiled files which options they were compiled under.  Unlike the previous version of this fingerprint, the mode theory is included: a file compiled under one mode theory contains marshaled modalities whose representation is specific to that theory, so loading it under another one would be unsound. *)
let marshal chan (t : t) = Marshal.to_channel chan t []
let unmarshal chan = (Marshal.from_channel chan : t)

(* The options in force for the current run, or None if they haven't been fixed yet.  They are fixed just before the first command that isn't an "option" command. *)
let current : t option ref = ref None
let installed () = !current
let set_installed t = current := Some t

(* Reading the options is an error before they are fixed; every caller runs during typechecking, which happens after. *)
let get () =
  match !current with
  | Some t -> t
  | None -> failwith "type theory options not yet fixed"
