(* A declarative registry of all the mode theories that can be selected by the user, either with a command-line flag or with an "option modal" command.  Previously this information was spread out among the imperative command-line flag handlers in bin/narya.ml, which poked a collection of mutable references; each flag set some of them, and the compatibility of the resulting combination was checked afterwards by replaying those references in order.  That made the error messages depend on the order in which the flags were written.  Here instead each theory declares its own requirements as data, so that a complete set of options can be validated all at once. *)

(* The name of a mode theory is a list of words, e.g. ["discrete"; "tconn"], so that it can be written in a source file as a sequence of identifier tokens without worrying about whether a hyphen would lex as part of an identifier. *)
type name = string list

(* Whether, and with what arity, a theory permits external parametricity.  [`None] means it doesn't; [`One] means it does but only at arity 1; [`Any] means it does at any arity. *)
type extern = [ `None | `One | `Any ]

(* Whether a theory restricts the arity of parametricity. *)
type arity_restriction = [ `One | `Any ]

type entry = {
  (* The canonical name, as written in an "option modal" command. *)
  name : name;
  (* Alternate names accepted for the same theory. *)
  aliases : name list;
  (* The corresponding command-line flag, without its leading dash.  Used in error messages, and to build the command-line flag list. *)
  flag : string;
  (* Install this theory's modes, modalities, and cells, with the given user-supplied renamings. *)
  install : string list -> string list -> string list -> unit;
  (* Whether this theory requires parametricity, i.e. forbids higher observational type theory. *)
  requires_parametric : bool;
  (* Whether this theory permits external parametricity. *)
  external_ok : extern;
  (* Whether this theory restricts the arity of parametricity. *)
  arity_ok : arity_restriction;
  (* A short description, for the command-line usage message. *)
  doc : string;
}

(* The default entry, which the individual theories below override.  Note that the default [external_ok] is [`None]: external parametricity requires a mode theory that explicitly permits it. *)
let default =
  {
    name = [ "trivial" ];
    aliases = [];
    flag = "trivial";
    install = Trivial.install;
    requires_parametric = false;
    external_ok = `None;
    arity_ok = `Any;
    doc = "The trivial mode theory (a single mode with no nontrivial modalities)";
  }

let all : entry list =
  [
    default;
    {
      default with
      name = [ "coreflector" ];
      aliases = [ [ "crisp" ] ];
      flag = "coreflector";
      install = Coreflector.install (module Coreflector.Ordinary : Coreflector.Variant);
      doc = "The coreflector mode theory";
    };
    {
      default with
      name = [ "discrete"; "coreflector" ];
      flag = "discrete-coreflector";
      install = Coreflector.install (module Coreflector.Discrete : Coreflector.Variant);
      requires_parametric = true;
      external_ok = `One;
      doc = "The discrete coreflector mode theory";
    };
    {
      default with
      name = [ "comonad" ];
      flag = "comonad";
      install = Comonad.install (module Comonad.Ordinary : Comonad.Variant);
      doc = "The comonad mode theory (a non-idempotent comonad ♭, not locally posetal)";
    };
    {
      default with
      name = [ "discrete"; "comonad" ];
      flag = "discrete-comonad";
      install = Comonad.install (module Comonad.Discrete : Comonad.Variant);
      requires_parametric = true;
      external_ok = `Any;
      doc = "The discrete comonad mode theory";
    };
    {
      default with
      name = [ "monad" ];
      flag = "monad";
      install = Monad_theory.install;
      doc = "The monad mode theory (a non-idempotent monad ♯, not locally posetal)";
    };
    {
      default with
      name = [ "reflector" ];
      flag = "reflector";
      install = Reflector.install;
      doc = "The reflector mode theory";
    };
    {
      default with
      name = [ "spatial" ];
      flag = "spatial";
      install = Spatial.install (module Spatial.Ordinary : Spatial.Variant);
      doc = "The spatial mode theory (coreflector ♭ left adjoint to reflector ♯)";
    };
    {
      default with
      name = [ "discrete"; "spatial" ];
      flag = "discrete-spatial";
      install = Spatial.install (module Spatial.Discrete : Spatial.Variant);
      requires_parametric = true;
      doc = "The spatial mode theory with discrete coreflector";
    };
    {
      default with
      name = [ "functor" ];
      flag = "functor";
      install = Functor.install (module Functor.Ordinary : Functor.Variant);
      doc = "The functor mode theory";
    };
    {
      default with
      name = [ "transparent"; "functor" ];
      flag = "transparent-functor";
      install = Functor.install (module Functor.Transparent : Functor.Variant);
      doc = "The transparent functor mode theory";
    };
    {
      default with
      name = [ "discrete"; "functor" ];
      flag = "discrete-functor";
      install = Functor.install (module Functor.Discrete : Functor.Variant);
      requires_parametric = true;
      doc = "The functor mode theory with discrete domain mode";
    };
    {
      default with
      name = [ "composable"; "functors" ];
      flag = "composable-functors";
      install = Composable_functors.install;
      doc = "The composable functors mode theory";
    };
    {
      default with
      name = [ "transformation" ];
      flag = "transformation";
      install = Transformation.install;
      doc = "The transformation mode theory (a single 2-cell ○ ⇒ ▱)";
    };
    {
      default with
      name = [ "composable"; "transformations" ];
      flag = "composable-transformations";
      install = Composable_transformations.install;
      doc = "The composable transformations mode theory (2-cells ○ ⇒ ▱ ⇒ ▹)";
    };
    {
      default with
      name = [ "interchange" ];
      flag = "interchange";
      install = Interchange.install;
      doc = "The interchange mode theory (2-cells ▹ ⇒ ◃ and ▸ ⇒ ◂ satisfying interchange)";
    };
    {
      default with
      name = [ "adjunction" ];
      flag = "adjunction";
      install = Adjunction.install (module Adjunction.Ordinary : Adjunction.Variant);
      doc = "The adjunction mode theory";
    };
    {
      default with
      name = [ "discrete"; "adjunction" ];
      flag = "discrete-adjunction";
      install = Adjunction.install (module Adjunction.Discrete : Adjunction.Variant);
      requires_parametric = true;
      external_ok = `Any;
      doc = "The adjunction mode theory with discrete left adjoint";
    };
    {
      default with
      name = [ "coreflection" ];
      flag = "coreflection";
      install = Coreflection.install (module Coreflection.Ordinary : Coreflection.Variant);
      doc = "The coreflection mode theory";
    };
    {
      default with
      name = [ "discrete"; "coreflection" ];
      flag = "discrete-coreflection";
      install = Coreflection.install (module Coreflection.Discrete : Coreflection.Variant);
      requires_parametric = true;
      external_ok = `One;
      doc = "The discrete coreflection mode theory";
    };
    {
      default with
      name = [ "guarded" ];
      flag = "guarded";
      install = Guarded.install;
      doc = "The guarded mode theory (coreflection plus a later modality on Type)";
    };
    {
      default with
      name = [ "local" ];
      flag = "local";
      install = Local.install (module Local.Ordinary : Local.Variant);
      doc = "The local geometric morphism mode theory";
    };
    {
      default with
      name = [ "discrete"; "local" ];
      flag = "discrete-local";
      install = Local.install (module Local.Discrete : Local.Variant);
      requires_parametric = true;
      doc = "The discrete local mode theory";
    };
    {
      default with
      name = [ "inconsistent"; "local" ];
      flag = "inconsistent-local";
      install = Local.install (module Local.Inconsistent : Local.Variant);
      requires_parametric = true;
      (* Hidden: this variant exists only to exhibit the inconsistency that the discrete local mode theory avoids, so it is deliberately left out of the usage message. *)
      doc = "";
    };
    {
      default with
      name = [ "tconn" ];
      flag = "tconn";
      install = Tconn.install (module Tconn.Ordinary : Tconn.Variant);
      doc = "The totally connected geometric morphism mode theory";
    };
    {
      default with
      name = [ "discrete"; "tconn" ];
      flag = "discrete-tconn";
      install = Tconn.install (module Tconn.Discrete : Tconn.Variant);
      requires_parametric = true;
      external_ok = `One;
      arity_ok = `One;
      doc = "The discrete tconn mode theory";
    };
    {
      default with
      name = [ "cospatial" ];
      flag = "cospatial";
      install = Cospatial.install (module Cospatial.Ordinary : Cospatial.Variant);
      doc = "The cospatial mode theory (reflector ♯ left adjoint to coreflector ♭)";
    };
    {
      default with
      name = [ "discrete"; "cospatial" ];
      flag = "discrete-cospatial";
      install = Cospatial.install (module Cospatial.Discrete : Cospatial.Variant);
      requires_parametric = true;
      external_ok = `One;
      arity_ok = `One;
      doc = "The cospatial mode theory with discrete coreflector";
    };
    {
      default with
      name = [ "ambiflector" ];
      flag = "ambiflector";
      install = Ambiflector.install (module Ambiflector.Ordinary : Ambiflector.Variant);
      doc = "The ambiflector mode theory (♮ is both a reflector and a coreflector)";
    };
    {
      default with
      name = [ "discrete"; "ambiflector" ];
      flag = "discrete-ambiflector";
      install = Ambiflector.install (module Ambiflector.Discrete : Ambiflector.Variant);
      requires_parametric = true;
      arity_ok = `One;
      doc = "The ambiflector mode theory with nonparametric ♮";
    };
    {
      default with
      name = [ "ambiflection" ];
      flag = "ambiflection";
      install = Ambiflection.install (module Ambiflection.Ordinary : Ambiflection.Variant);
      doc = "The ambiflection mode theory (△ and □ are each both a reflector and a coreflector)";
    };
    {
      default with
      name = [ "discrete"; "ambiflection" ];
      flag = "discrete-ambiflection";
      install = Ambiflection.install (module Ambiflection.Discrete : Ambiflection.Variant);
      requires_parametric = true;
      arity_ok = `One;
      doc = "The ambiflection mode theory with nonparametric Disc";
    };
    {
      default with
      name = [ "gwpt" ];
      flag = "gwpt";
      install = Gwpt.install (module Gwpt.Ordinary : Gwpt.Variant);
      doc = "The geometrically well-pointed topos mode theory";
    };
    {
      default with
      name = [ "discrete"; "gwpt" ];
      flag = "discrete-gwpt";
      install = Gwpt.install (module Gwpt.Discrete : Gwpt.Variant);
      requires_parametric = true;
      external_ok = `Any;
      doc = "The discrete gwpt mode theory";
    };
  ]

(* The name of the default (trivial) mode theory, which is what a source file asserts by not containing any "option modal" command. *)
let trivial = default.name
let to_string (name : name) = String.concat " " name

(* Look up a theory by name, accepting any of its aliases. *)
let find (name : name) : entry option =
  List.find_opt (fun e -> e.name = name || List.mem name e.aliases) all

(* Look up a theory by its command-line flag name (without the leading dash). *)
let find_flag (flag : string) : entry option = List.find_opt (fun e -> e.flag = flag) all

(* All the names, canonical and aliases alike, for error messages. *)
let all_names () = List.concat_map (fun e -> e.name :: e.aliases) all
