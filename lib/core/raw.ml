open Util
open Dim
open Modal
include Energy
include Indices

type 'a located = 'a Asai.Range.located

let locate_opt = Asai.Range.locate_opt
let locate_map f ({ value; loc } : 'a located) = locate_opt loc (f value)

(* Raw (unchecked) terms, using intrinsically well-scoped De Bruijn indices, and separated into synthesizing terms and checking terms.  These match the user-facing syntax rather than the internal syntax.  In particular, applications, abstractions, and pi-types are all unary, there is only one universe, and the only operator actions are refl (including Id) and sym. *)

(* Where an ImplicitApp gets its implicit first argument: the type being checked against itself, or the argument at the given (0-based) position of the constant that type is an application of, such as P in "forall ℕ P".  This is a stopgap until we have unification. *)
type implicit_source = [ `Goal | `Goal_arg of int ]

module rec Make : functor (I : Indices) -> sig
  module Namevec : module type of Namevec (I)
  module Patternvars : module type of Patternvars (I)
  include module type of Namevec.P

  type 'a index = 'a I.index * any_sface option

  type _ synth =
    | Var : 'a index -> 'a synth
    | Const : Constant.t -> 'a synth
    | Field :
        'a synth located
        * [ `Name of string * int list | `Int of int ]
        * string located list located option
        -> 'a synth
    | Key : 'a synth located * string list located -> 'a synth
    | Pi :
        I.name * string located list located * 'a check located * 'a I.suc check located
        -> 'a synth
    | HigherPi :
        I.name * string located list located * 'a synth located * 'a I.suc synth located
        -> 'a synth
    | InstHigherPi : 'n D.pos * ('a, 'b, 'ab) tel * 'ab check located -> 'a synth
    | App :
        'a check located * 'a check option located * [ `Implicit | `Explicit ] located
        -> 'a synth
    | Asc : 'a check located * 'a check located -> 'a synth
    | AscLam :
        I.name located * string located list located * 'a check located * 'a I.suc synth located
        -> 'a synth
    | UU : 'mode Mode.t -> 'a synth
    | Let :
        I.name * string located list located * 'a synth located * 'a I.suc check located
        -> 'a synth
    | Letrec : ('a, 'b, 'ab) tel * ('ab check located, 'b) Vec.t * 'ab check located -> 'a synth
    | Act : string located * ('m, 'n) deg * 'a check located option -> 'a synth
    | Match : {
        tm : 'a synth located;
        window : string located list located option;
        sort : [ `Implicit | `Explicit of 'a check located | `Nondep of int located ];
        branches : (Constr.t, 'a branch) Abwd.t;
        refutables : 'a refutables option;
        highers : bool ref located list;
      }
        -> 'a synth
    | Fail : Reporter.Code.t -> 'a synth
    | ImplicitSApp : 'a synth located * Asai.Range.t option * 'a synth located -> 'a synth
    | SFirst :
        ([ `Data of Constr.t list | `Codata of string list | `Any ] * 'a synth * bool) list
        * 'a synth option
        -> 'a synth
    | Calc :
        'a synth located
        * ('a check located * ('a check located * [ `Plain | `Reversed ]) option) list
        -> 'a synth

  and _ check =
    | Synth : 'a synth -> 'a check
    | Lam : {
        name : I.name located;
        cube : [ `Cube of (D.wrapped * Asai.Range.t option) option ref | `Normal ] located;
        implicit : [ `Explicit | `Implicit ];
        dom : (string located list located * 'a check located) option;
        body : 'a I.suc check located;
      }
        -> 'a check
    | Struct :
        ('s, 'et) eta
        * ((string * string list) option, [ `Normal | `Cube ] located * 'a check located) Abwd.t
        -> 'a check
    | Constr :
        Constr.t located * ('a check located * [ `Implicit | `Explicit ] located) list
        -> 'a check
    | Numeral : Q.t -> 'a check
    | Empty_co_match : 'a check
    | Data : (Constr.t, 'a dataconstr located) Abwd.t * Variables.hints -> 'a check
    | Codata : (Field.wrapped, 'a codatafield) Abwd.t * Variables.hints -> 'a check
    | Record :
        ('a, 'c, 'ac) Namevec.t located * ('ac, 'd, 'acd) tel * opacity * Variables.hints
        -> 'a check
    | SelfRecord : (Field.wrapped, 'a codatafield) Abwd.t * opacity * Variables.hints -> 'a check
    | Refute :
        ('a synth located * string located list located option) list * [ `Explicit | `Implicit ]
        -> 'a check
    | Hole : {
        scope : 'a I.scope;
        loc : Asai.Range.t;
        li : No.interval;
        ri : No.interval;
        num : int ref;
      }
        -> 'a check
    | Realize : 'a check -> 'a check
    | ImplicitApp :
        'a synth located * implicit_source * (Asai.Range.t option * 'a check located) list
        -> 'a check
    | Embed : 'a I.embed -> 'a check
    | First :
        ([ `Data of Constr.t list | `Codata of string list | `Any ] * 'a check * bool) list
        -> 'a check
    | Oracle : 'a check located -> 'a check
    | Weaken : 'a check * ('a I.suc, 'b) Eq.t -> 'b check

  and _ branch =
    | Branch :
        ('a, 'b, 'ab) Patternvars.t located
        * [ `Normal of Asai.Range.t option | `Cube of bool ref located list ]
        * 'ab check located
        -> 'a branch

  and _ dataconstr = Dataconstr : ('a, 'b, 'ab) tel * 'ab check located option -> 'a dataconstr

  and _ codatafield =
    | Codatafield :
        I.name
        * string located list located option
        * 'a check located option
        * 'a I.suc check located
        -> 'a codatafield

  and 'a refutables = {
    refutables : 'b 'ab. ('a, 'b, 'ab) Namevec.P.bplus -> 'ab synth located list;
  }

  and (_, _, _) tel =
    | Emp : ('a, Fwn.zero, 'a) tel
    | Ext :
        I.name * string located list located * 'a check located * ('a I.suc, 'b, 'ab) tel
        -> ('a, 'b Fwn.suc, 'ab) tel

  val fwn_of_tel : ('a, 'b, 'c) tel -> 'b Fwn.t
  val mods_of_tel : ('a, 'b, 'c) tel -> string located list located list
end =
functor
  (I : Indices)
  ->
  struct
    module Namevec = Namevec (I)
    module Patternvars = Patternvars (I)
    include Namevec.P

    (* A raw De Bruijn index is a well-scoped (backwards) natural number (or, more generally, an element of I.index) together with a possible face.  During typechecking we will verify that the face, if given, is applicable to the variable as a "cube variable", and compile the combination into a more strongly well-scoped kind of index. *)
    type 'a index = 'a I.index * any_sface option

    (* Synthesizable raw terms *)
    type _ synth =
      | Var : 'a index -> 'a synth
      | Const : Constant.t -> 'a synth
      (* A field projection from a possibly-higher-coinductive type comes with a suffix that is a string of integers, denoting a partial bijection between n and m that is total on n.  This is the same as an injection from n to m, or equivalently an insertion of n into m∖l to produce m, where l = image(n). *)
      (* A modal field projection additionally records the name of the locking modality (the left adjoint of the field's adjunction), specified by the user with a modal variable ascription such as "(x : f | _) .fld". *)
      | Field :
          'a synth located
          * [ `Name of string * int list | `Int of int ]
          * string located list located option
          -> 'a synth
      (* A modal key operation applied postfix to a synthesizing term, written "x #a.b.c".  The dot-separated pieces of the key name are stored as strings, to be resolved into a 2-cell at typechecking time. *)
      | Key : 'a synth located * string list located -> 'a synth
      | Pi :
          I.name * string located list located * 'a check located * 'a I.suc check located
          -> 'a synth
      | HigherPi :
          I.name * string located list located * 'a synth located * 'a I.suc synth located
          -> 'a synth
      (* An n-dimensional pi-type, fully instantiated, with all its domains supplied.  The dimension 'n is the outer (unfiltered) dimension; the domains form a telescope whose length must match the number of faces of the *filtered* dimension, which is not known until typechecking (since parsing the modality annotations requires knowing the modes). *)
      | InstHigherPi : 'n D.pos * ('a, 'b, 'ab) tel * 'ab check located -> 'a synth
      (* The location of the implicitness flag is, in the implicit case, the location of the braces surrounding the implicit argument. *)
      | App :
          'a check located * 'a check option located * [ `Implicit | `Explicit ] located
          -> 'a synth
      | Asc : 'a check located * 'a check located -> 'a synth
      (* Abstraction with ascribed variable and synthesizing body.  Currently can't be a cube or implicit.  *)
      | AscLam :
          I.name located * string located list located * 'a check located * 'a I.suc synth located
          -> 'a synth
      (* A universe knows its mode. *)
      | UU : 'mode Mode.t -> 'a synth
      (* A Let can either synthesize or (sometimes) check.  It synthesizes only if its body also synthesizes, but we wait until typechecking type to look for that, so that if it occurs in a checking context the body can also be checking.  Thus, we make it a "synthesizing term".  The term being bound must also synthesize; the shorthand notation "let x : A := M" is expanded during parsing to "let x := M : A". *)
      | Let :
          I.name * string located list located * 'a synth located * 'a I.suc check located
          -> 'a synth
      (* Letrec has a telescope of types, so that each can depend on the previous ones, and an equal-length vector of bound terms, all in the context extended by all the variables being bound, plus a body that is also in that context. *)
      | Letrec : ('a, 'b, 'ab) tel * ('ab check located, 'b) Vec.t * 'ab check located -> 'a synth
      (* An Act can also often check, but can also synthesizes if its body does.  *)
      | Act : string located * ('m, 'n) deg * 'a check located option -> 'a synth
      (* A Match can also sometimes check, but synthesizes if it has an explicit return type or if it is nondependent and its first branch synthesizes. *)
      | Match : {
          tm : 'a synth located;
          (* An optionally specified window modality *)
          window : string located list located option;
          (* Implicit means no "return" statement was given, so Narya has to guess what to do.  Explicit means a "return" statement was given with a motive.  "Nondep" means a placeholder return statement like "_ ↦ _" was given, indicating that a non-dependent matching is intended (to silence hints about fallback from the implicit case). *)
          sort : [ `Implicit | `Explicit of 'a check located | `Nondep of int located ];
          branches : (Constr.t, 'a branch) Abwd.t;
          refutables : 'a refutables option;
          (* If this is the "master" controlling match in a family of matches generated by a multiple/deep match, record all the toggles for all the ⤇ matches to check that they actually contain something higher-dimensional *)
          highers : bool ref located list;
        }
          -> 'a synth
      | Fail : Reporter.Code.t -> 'a synth
      (* Pass the synthesized type of an argument as an implicit first argument of a function. *)
      | ImplicitSApp : 'a synth located * Asai.Range.t option * 'a synth located -> 'a synth
      (* Try several terms, testing for each whether the synthesized type of the specified term has certain constructors or fields. *)
      | SFirst :
          ([ `Data of Constr.t list | `Codata of string list | `Any ] * 'a synth * bool) list
          * 'a synth option
          -> 'a synth
      (* Chain of equational reasoning.  Each step has a term and an optional proof.  A proof marked `Reversed proves the equality in the opposite orientation. *)
      | Calc :
          'a synth located
          * ('a check located * ('a check located * [ `Plain | `Reversed ]) option) list
          -> 'a synth

    (* Checkable raw terms *)
    and _ check =
      | Synth : 'a synth -> 'a check
      (* An abstraction knows whether it is a cube abstraction (⤇) or a normal one (↦).  In the former case it stores an optional dimension, so that multiple variables in the same abstraction (x y ⤇) can be enforced to be the same dimension, and the location of the previous variable that set the dimension. *)
      | Lam : {
          name : I.name located;
          cube : [ `Cube of (D.wrapped * Asai.Range.t option) option ref | `Normal ] located;
          implicit : [ `Explicit | `Implicit ];
          (* An abstraction can have its variable ascribed to a type.  If in addition the body is synthesizing, then it is a synthesizing term called AscLam.  If the body is only checking, then it's still a Lam, but with a "dom" supplied here. *)
          dom : (string located list located * 'a check located) option;
          body : 'a I.suc check located;
        }
          -> 'a check
      (* A "Struct" is our current name for both tuples and comatches, which share a lot of their implementation even though they are conceptually and syntactically distinct.  Those with eta=`Eta are tuples, those with eta=`Noeta are comatches.  We index them by an option so as to include any unlabeled fields, with their relative order to the labeled ones.  The field hasn't been interned to an intrinsic dimension yet (that depends on what it checks against), so it's just a string name, plus a list of strings to indicate a pbij for higher fields.  We also store whether they were defined with a ↦ or a ⤇. *)
      | Struct :
          ('s, 'et) eta
          * ((string * string list) option, [ `Normal | `Cube ] located * 'a check located) Abwd.t
          -> 'a check
      (* The arguments of a constructor application.  In the higher-dimensional case the user may optionally supply the redundant boundary arguments of each argument's cube, as implicit arguments preceding the explicit top-dimensional one; they are then checked against the boundary extracted from the type being checked against. *)
      | Constr :
          Constr.t located * ('a check located * [ `Implicit | `Explicit ] located) list
          -> 'a check
      | Numeral : Q.t -> 'a check
      (* "[]", which could be either an empty pattern-matching lambda or an empty comatch *)
      | Empty_co_match : 'a check
      | Data : (Constr.t, 'a dataconstr located) Abwd.t * Variables.hints -> 'a check
      (* A codatatype binds one more "self" variable in the types of each of its fields.  For a higher-dimensional codatatype (like a codata version of Gel), this becomes a cube of variables.  The field also knows its dimension already. *)
      | Codata : (Field.wrapped, 'a codatafield) Abwd.t * Variables.hints -> 'a check
      (* A record type binds its "self" variable namelessly, exposing it to the user by additional variables that are bound locally to its fields.  This can't be "cubeified" as easily, so we have the user specify a list of ordinary variables to be its boundary.  Thus, in practice below 'c must be a number of faces associated to a dimension, but the parser doesn't know the dimension, so it can't ensure that.  The unnamed internal variable is included as the last one. *)
      | Record :
          ('a, 'c, 'ac) Namevec.t located * ('ac, 'd, 'acd) tel * opacity * Variables.hints
          -> 'a check
      (* There's also a notation for record types that uses self variables like codata. *)
      | SelfRecord : (Field.wrapped, 'a codatafield) Abwd.t * opacity * Variables.hints -> 'a check
      (* Empty match against the first one of the arguments belonging to an empty type.  Each argument carries an optional window modality. *)
      | Refute :
          ('a synth located * string located list located option) list * [ `Explicit | `Implicit ]
          -> 'a check
      (* A hole must store the entire "state" from when it was entered, so that the user can later go back and fill it with a term that would have been valid in its original position.  This includes the variables in lexical scope, which are available only during parsing, so we store them here at that point.  During typechecking, when the actual metavariable is created, we save the lexical scope along with its other context and type data.  A hole also stores its source location so that proofgeneral can create an overlay at that place, and the notation tightnesses of the hole location. *)
      | Hole : {
          scope : 'a I.scope;
          loc : Asai.Range.t;
          li : No.interval;
          ri : No.interval;
          num : int ref;
        }
          -> 'a check
      (* Force a leaf of the case tree *)
      | Realize : 'a check -> 'a check
      (* Pass the type being checked against, or one of the arguments of the constant it is an application of, as the implicit first argument of a function. *)
      | ImplicitApp :
          'a synth located * implicit_source * (Asai.Range.t option * 'a check located) list
          -> 'a check
      (* Embed an arbitrary object *)
      | Embed : 'a I.embed -> 'a check
      (* Try several terms, testing for each whether the goal type has certain constructors or fields. *)
      | First :
          ([ `Data of Constr.t list | `Codata of string list | `Any ] * 'a check * bool) list
          -> 'a check
      (* Check a term, but then verify its correctness with an external oracle. *)
      | Oracle : 'a check located -> 'a check
      (* Lift a term to a longer context *)
      | Weaken : 'a check * ('a I.suc, 'b) Eq.t -> 'b check

    (* The location of the pattern variables is that of the whole pattern.  The location of the cube flag is that of the mapsto. *)
    and _ branch =
      | Branch :
          ('a, 'b, 'ab) Patternvars.t located
          (* The ref argument to `Cube records whether any of the matches in this ⤇ group are *actually* higher-dimensional, so we can raise an error if they're not. *)
          * [ `Normal of Asai.Range.t option | `Cube of bool ref located list ]
          * 'ab check located
          -> 'a branch

    (* *)
    and _ dataconstr = Dataconstr : ('a, 'b, 'ab) tel * 'ab check located option -> 'a dataconstr

    (* A field of a codatatype has a self variable and a type.  At the raw level we don't need any more information about higher fields. *)
    (* A codata field records the name of the locking modality (the left adjoint of its adjunction), if any, specified by the user with a modal ascription of the self variable such as "(x :f| _) .fld : A".  The type can be supplied instead of a placeholder. *)
    and _ codatafield =
      | Codatafield :
          I.name
          * string located list located option
          * 'a check located option
          * 'a I.suc check located
          -> 'a codatafield

    (* A raw match stores the information about the pattern variables available from previous matches that could be used to refute missing cases.  But it can't store them as raw terms, since they have to be in the correct context extended by the new pattern variables generated in any such case.  So it stores them as a callback that puts them in any such extended context. *)
    and 'a refutables = { refutables : 'b 'ab. ('a, 'b, 'ab) bplus -> 'ab synth located list }

    (* An ('a, 'b, 'ab) tel is a raw telescope of length 'b in context 'a, with 'ab = 'a+'b the extended context. *)
    and (_, _, _) tel =
      | Emp : ('a, Fwn.zero, 'a) tel
      | Ext :
          I.name * string located list located * 'a check located * ('a I.suc, 'b, 'ab) tel
          -> ('a, 'b Fwn.suc, 'ab) tel

    (* The length of a telescope is a forwards nat. *)
    let rec fwn_of_tel : type a b c. (a, b, c) tel -> b Fwn.t = function
      | Emp -> Zero
      | Ext (_, _, _, tel) -> Suc (fwn_of_tel tel)

    (* The modality annotations of the entries of a telescope. *)
    let rec mods_of_tel : type a b c. (a, b, c) tel -> string located list located list = function
      | Emp -> []
      | Ext (_, modality, _, tel) -> modality :: mods_of_tel tel
  end

module Indexed = Make (DeBruijnIndices)

(* We supply a generic name-resolution module that turns explicit names into De Bruijn indices, threading through a scope of bound variables.  In fact, it is more straightforward to implement a general translation operation that turns raw terms for one implementation of Indices into those for another.  For this we need an additional parameter module.  *)

module type Resolver = sig
  module I1 : Indices
  module I2 : Indices

  module T1 : module type of struct
    include Make (I1)
  end

  module T2 : module type of struct
    include Make (I2)
  end

  type ('a1, 'a2) scope

  (* What we need is basically the ability to look up names and indices to translate them.  Typically this will be a vector of explicit names used to translate in one direction or the other between names and nat-indices.  *)
  val reindex : ('a1, 'a2) scope -> 'a1 I1.index -> ('a2 I2.index, Reporter.Code.t) Result.t
  val rename : ('a1, 'a2) scope -> I1.name -> I2.name

  (* We also need to be able to translate the 'scopes' that appear in Holes. *)
  val rescope : ('a1, 'a2) scope -> 'a1 I1.scope -> 'a2 I2.scope

  (* This is how we extend a scope when passing under a binder. *)
  val snoc : ('a1, 'a2) scope -> I1.name -> ('a1 I1.suc, 'a2 I2.suc) scope

  (* Remove the last element of a scope *)
  type (_, _) pop = Pop : ('a1, 'a2) scope * ('a2 I2.suc, 'a2s) Eq.t -> ('a1, 'a2s) pop

  val pop : ('a1 I1.suc, 'a2) scope -> ('a1, 'a2) pop

  (* This is for annotations and saving all the seen scopes. *)
  val visit : ('a1, 'a2) scope -> 'a2 T2.check located -> unit

  (* Deal with embedded objects, possibly recursively *)
  val embed : ('a1, 'a2) scope -> 'a1 I1.embed -> ('a1 T1.check, 'a2 T2.check) Either.t
end

(* Resolution is basically a straightforward structural induction that walks the terms, extending the scope as it goes. *)
module Resolve (R : Resolver) = struct
  (* We can't make things more concise with aliases like
       module I1 = R.I1
     because module aliases are not preserved by functors: F(I1) will not be equal to F(R.I1). *)

  (* The result of renaming the pattern variables of a match branch: the renamed variables, in the target index type, along with the scope extended by them. *)
  type (_, _, _) resolve_pv =
    | Resolve_pv :
        ('a2, 'b, 'ab2) R.T2.Patternvars.t * ('ab1, 'ab2) R.scope
        -> ('a2, 'b, 'ab1) resolve_pv

  let rec append : type a1 a2 b ab1 ab2.
      (a1, a2) R.scope ->
      (a1, b, ab1) R.T1.Namevec.t ->
      (a2, b, ab2) R.T2.bplus ->
      (ab1, ab2) R.scope =
   fun ctx xs ab2 ->
    match xs with
    | [] ->
        let Eq = R.T2.bplus_zero ab2 in
        ctx
    | x :: xs ->
        let ab2 = R.T2.bplus_suc ab2 in
        append (R.snoc ctx x) xs ab2

  let rec renames : type a1 a2 b ab1 ab2.
      (a1, a2) R.scope ->
      (a1, b, ab1) R.T1.Namevec.t ->
      (a2, b, ab2) R.T2.bplus ->
      (a2, b, ab2) R.T2.Namevec.t =
   fun ctx xs ab ->
    match xs with
    | [] ->
        let Eq = R.T2.bplus_zero ab in
        []
    | x :: xs ->
        let ab = R.T2.bplus_suc ab in
        R.rename ctx x :: renames (R.snoc ctx x) xs ab

  let rec synth : type a1 a2. (a1, a2) R.scope -> a1 R.T1.synth located -> a2 R.T2.synth located =
   fun ctx tm ->
    let newtm : a2 R.T2.synth =
      match tm.value with
      | Var (name, fa) -> (
          (* Here's the important resolution bit: we "look up" names in the scope (although at this point that is just an abstract operation supplied by the caller), and insert an error in case of failure.  Note that we store the error in the term rather than raising it immediately; a caller who wants to raise it immediately can do that in the function 'scope_error' instead of returning it. *)
          match R.reindex ctx name with
          | Ok ix -> Var (ix, fa)
          | Error e -> Fail e)
      | Const c -> Const c
      | Field (tm, fld, lock) -> Field (synth ctx tm, fld, lock)
      | Key (tm, parts) -> Key (synth ctx tm, parts)
      | Pi (x, modality, dom, cod) ->
          Pi (R.rename ctx x, modality, check ctx dom, check (R.snoc ctx x) cod)
      | HigherPi (x, modality, dom, cod) ->
          HigherPi (R.rename ctx x, modality, synth ctx dom, synth (R.snoc ctx x) cod)
      | InstHigherPi (n, doms, cod) ->
          let (Bplus ab) = R.T2.bplus (R.T1.fwn_of_tel doms) in
          let doms2, ctx2 = tel ctx doms ab in
          InstHigherPi (n, doms2, check ctx2 cod)
      | App (fn, arg, impl) ->
          let arg =
            match arg.value with
            | Some x ->
                let arg = check ctx (locate_opt arg.loc x) in
                locate_opt arg.loc (Some arg.value)
            | None -> locate_opt arg.loc None in
          App (check ctx fn, arg, impl)
      | Asc (tm, ty) -> Asc (check ctx tm, check ctx ty)
      | AscLam (x, modality, dom, body) ->
          AscLam
            (locate_map (R.rename ctx) x, modality, check ctx dom, synth (R.snoc ctx x.value) body)
      | UU mode -> UU mode
      | Let (x, modality, tm, body) ->
          Let (R.rename ctx x, modality, synth ctx tm, (check (R.snoc ctx x)) body)
      | Letrec (tys, tms, body) ->
          let (Bplus ab) = R.T2.bplus (Vec.length tms) in
          let tys2, ctx2 = tel ctx tys ab in
          let tms2 = Vec.map (check ctx2) tms in
          Letrec (tys2, tms2, check ctx2 body)
      | Act (s, fa, tm) -> Act (s, fa, Option.map (check ctx) tm)
      | Match { tm; window; sort; branches; refutables = r; highers } ->
          let tm = synth ctx tm in
          let sort =
            match sort with
            | `Explicit ty -> `Explicit (check ctx ty)
            | `Nondep i -> `Nondep i
            | `Implicit -> `Implicit in
          let branches = Abwd.map (branch ctx) branches in
          let refutables = Option.map (refutables ctx) r in
          Match { tm; window; sort; branches; refutables; highers }
      | Fail e -> Fail e
      | ImplicitSApp (fn, apploc, arg) -> ImplicitSApp (synth ctx fn, apploc, synth ctx arg)
      | SFirst (tms, arg) ->
          SFirst
            ( List.map (fun (t, x, b) -> (t, (synth ctx (locate_opt tm.loc x)).value, b)) tms,
              Option.map (fun arg -> (synth ctx (locate_opt tm.loc arg)).value) arg )
      | Calc (first, rest) ->
          Calc
            ( synth ctx first,
              List.map
                (fun (y, xeqy) ->
                  (check ctx y, Option.map (fun (e, dir) -> (check ctx e, dir)) xeqy))
                rest ) in
    R.visit ctx (locate_opt tm.loc (R.T2.Synth newtm));
    locate_opt tm.loc newtm

  and check : type a1 a2. (a1, a2) R.scope -> a1 R.T1.check located -> a2 R.T2.check located =
   fun ctx tm ->
    let newtm : a2 R.T2.check =
      match tm.value with
      | Synth x -> Synth (synth ctx (locate_opt tm.loc x)).value
      | Lam { name; cube; implicit; dom; body } ->
          Lam
            {
              name = locate_map (R.rename ctx) name;
              cube;
              implicit;
              dom = Option.map (fun (mu, dom) -> (mu, check ctx dom)) dom;
              body = check (R.snoc ctx name.value) body;
            }
      | Struct (eta, fields) ->
          Struct (eta, Abwd.map (fun (cube, tm) -> (cube, check ctx tm)) fields)
      | Constr (c, args) -> Constr (c, List.map (fun (tm, i) -> (check ctx tm, i)) args)
      | Numeral x -> Numeral x
      | Empty_co_match -> Empty_co_match
      | Data (constrs, hints) -> Data (Abwd.map (locate_map (dataconstr ctx)) constrs, hints)
      | Codata (fields, hints) ->
          Codata
            ( Abwd.map
                (fun (R.T1.Codatafield (x, lock, ty, fld)) ->
                  R.T2.Codatafield
                    (R.rename ctx x, lock, Option.map (check ctx) ty, check (R.snoc ctx x) fld))
                fields,
              hints )
      | SelfRecord (fields, opaq, hints) ->
          SelfRecord
            ( Abwd.map
                (fun (R.T1.Codatafield (x, lock, ty, fld)) ->
                  R.T2.Codatafield
                    (R.rename ctx x, lock, Option.map (check ctx) ty, check (R.snoc ctx x) fld))
                fields,
              opaq,
              hints )
      | Record (xs, fields, opaq, hints) ->
          let (Bplus ac2) = R.T2.bplus (R.T1.Namevec.length xs.value) in
          let xs2 = renames ctx xs.value ac2 in
          let ctx2 = append ctx xs.value ac2 in
          let (Bplus ad) = R.T2.bplus (R.T1.fwn_of_tel fields) in
          let fields2, _ = tel ctx2 fields ad in
          Record (locate_opt xs.loc xs2, fields2, opaq, hints)
      | Refute (args, sort) -> Refute (List.map (fun (tm, w) -> (synth ctx tm, w)) args, sort)
      | Hole { scope; loc; li; ri; num } -> Hole { scope = R.rescope ctx scope; loc; li; ri; num }
      | Realize x -> Realize (check ctx (locate_opt tm.loc x)).value
      | ImplicitApp (fn, src, args) ->
          ImplicitApp (synth ctx fn, src, List.map (fun (l, x) -> (l, check ctx x)) args)
      | Embed e -> (
          match R.embed ctx e with
          | Left x -> (check ctx (locate_opt tm.loc x)).value
          | Right x -> x)
      | First tms ->
          First (List.map (fun (t, x, b) -> (t, (check ctx (locate_opt tm.loc x)).value, b)) tms)
      | Oracle tm -> Oracle (check ctx tm)
      | Weaken (x, Eq) ->
          let (Pop (ctx, Eq)) = R.pop ctx in
          Weaken ((check ctx (locate_opt tm.loc x)).value, Eq) in
    let newtm = locate_opt tm.loc newtm in
    R.visit ctx newtm;
    newtm

  and branch : type a1 a2. (a1, a2) R.scope -> a1 R.T1.branch -> a2 R.T2.branch =
   fun ctx (Branch (xs, cube, body)) ->
    let (Resolve_pv (xs2, ctx2)) = patternvars ctx xs.value in
    Branch (locate_opt xs.loc xs2, cube, check ctx2 body)

  (* Renaming the pattern variables of a match branch, unlike a Namevec, doesn't have a bplus supplied by the caller, since the extended context depends on how many of the arguments have explicit boundaries.  So we compute the renamed pattern variables and the extended scope together, with the extended index existential. *)
  and patternvars : type a1 a2 b ab1.
      (a1, a2) R.scope -> (a1, b, ab1) R.T1.Patternvars.t -> (a2, b, ab1) resolve_pv =
   fun ctx xs ->
    match xs with
    | [] -> Resolve_pv ([], ctx)
    | Cube x :: xs ->
        let x2 = R.rename ctx x in
        let (Resolve_pv (xs2, ctx2)) = patternvars (R.snoc ctx x) xs in
        Resolve_pv (Cube x2 :: xs2, ctx2)
    | Boundary ns :: xs ->
        let (Bplus ac) = R.T2.bplus (R.T1.Namevec.length ns.value) in
        let ns2 = renames ctx ns.value ac in
        let (Resolve_pv (xs2, ctx2)) = patternvars (append ctx ns.value ac) xs in
        Resolve_pv (Boundary (locate_opt ns.loc ns2) :: xs2, ctx2)

  and dataconstr : type a1 a2. (a1, a2) R.scope -> a1 R.T1.dataconstr -> a2 R.T2.dataconstr =
   fun ctx (Dataconstr (args, body)) ->
    let (Bplus ab) = R.T2.bplus (R.T1.fwn_of_tel args) in
    let args2, ctx2 = tel ctx args ab in
    Dataconstr (args2, Option.map (check ctx2) body)

  and refutables : type a1 a2. (a1, a2) R.scope -> a1 R.T1.refutables -> a2 R.T2.refutables =
   fun ctx { refutables } ->
    let refutables : type b ab2. (a2, b, ab2) R.T2.bplus -> ab2 R.T2.synth located list =
     fun ab2 ->
      let (Bplus ab1) = R.T1.bplus (R.T2.bplus_right ab2) in
      let ctx2 = append ctx (R.T1.Namevec.none ab1) ab2 in
      List.map (synth ctx2) (refutables ab1) in
    { refutables }

  and tel : type b a1 ab1 a2 ab2.
      (a1, a2) R.scope ->
      (a1, b, ab1) R.T1.tel ->
      (a2, b, ab2) R.T2.bplus ->
      (a2, b, ab2) R.T2.tel * (ab1, ab2) R.scope =
   fun ctx tele ab ->
    match tele with
    | Emp ->
        let Eq = R.T2.bplus_zero ab in
        (Emp, ctx)
    | Ext (x, modality, ty, rest) ->
        let ctx2 = R.snoc ctx x in
        let ab = R.T2.bplus_suc ab in
        let rest3, ctx3 = tel ctx2 rest ab in
        (Ext (R.rename ctx x, modality, check ctx ty, rest3), ctx3)
end

(* Since the De Bruijn index version is the standard one, we include that here. *)
include Indexed

(* Some utility functions specialized to the Indexed case. *)

let rec namevec_of_vec : type a b ab.
    (a, b, ab) Fwn.bplus -> (string option, b) Vec.t -> (a, b, ab) Namevec.t =
 fun ab xs ->
  match (ab, xs) with
  | Zero, [] -> []
  | Suc ab, x :: xs -> x :: namevec_of_vec ab xs

(* We end with some useful lemmas. *)

let rec dataconstr_of_pi : type a. a check located -> a dataconstr =
 fun ty ->
  match ty.value with
  | Synth (Pi (x, modality, dom, cod)) ->
      let (Dataconstr (tel, out)) = dataconstr_of_pi cod in
      Dataconstr (Ext (x, modality, dom, tel), out)
  | _ -> Dataconstr (Emp, Some ty)

(* Produces only explicit lambdas. *)
let rec lams : type a b ab.
    (a, b, ab) Indexed.bplus ->
    (string option located, b) Vec.t ->
    ab check located ->
    Asai.Range.t option ->
    a check located =
 fun ab xs tm loc ->
  match (ab, xs) with
  | Zero, [] -> tm
  | Suc ab, name :: xs ->
      {
        value =
          Lam
            {
              name;
              cube = locate_opt None `Normal;
              implicit = `Explicit;
              dom = None;
              body = lams ab xs tm loc;
            };
        loc;
      }

let rec bplus_of_tel : type a b c. (a, b, c) tel -> (a, b, c) Fwn.bplus = function
  | Emp -> Zero
  | Ext (_, _, _, tel) -> Suc (bplus_of_tel tel)
