open Util
open Tbwd
open Dim
open Core
open Term
module StringSet = Set.Make (String)

let __ANONYMOUS_VARIABLE__ = "_H"

(* Track the used variable names, to generate fresh ones for bound variables if needed. *)

(* We store a parametrized list of cubes of variable names like a context, along with a mapping of field names to local variable names bound textually to that field of the variable. *)
type 'b ctx =
  | Emp : emp ctx
  | Snoc : 'b ctx * 'n variables * (string, string) Abwd.t -> ('b, 'n) snoc ctx

(* We also store a set of which variables already exist, so that we can be sure of creating a new unused one. *)
type 'b t = { ctx : 'b ctx; used : StringSet.t }

let empty : emp t = { ctx = Emp; used = StringSet.empty }

let rec remove_ctx : type a n b. b ctx -> (a, n, b) Tbwd.insert -> a ctx =
 fun ctx i ->
  match (ctx, i) with
  | Snoc (ctx, vars, flds), Later i -> Snoc (remove_ctx ctx i, vars, flds)
  | Snoc (ctx, _, _), Now -> ctx
  | Emp, _ -> .

let remove : type a n b. b t -> (a, n, b) Tbwd.insert -> a t =
 fun { ctx; used } i -> { ctx = remove_ctx ctx i; used }

let cubevar x fa : string list =
  let fa = string_of_sface fa in
  if fa = "" then [ x ] else [ x; fa ]

(* Look up an index variable to find a name for it. *)
let lookup : type n. n t -> n index -> string list =
 fun { ctx; used = _ } x ->
  let rec lookup : type n. n ctx -> n index -> string list =
   fun ctx x ->
    match (ctx, x) with
    | Emp, _ -> .
    | Snoc (ctx, _, _), Index (Later x, fa) -> lookup ctx (Index (x, fa))
    | Snoc (_, Variables (_, mn, xs), _), Index (Now, fa) -> (
        let (SFace_of_plus (_, fb, fc)) = sface_of_plus mn fa in
        match NICubeOf.find xs fc with
        | Some x -> cubevar x fb
        | None -> [ __ANONYMOUS_VARIABLE__ ]) in
  lookup ctx x

(* Look up an index variable together with a field, to find a name for the combination, if there is one. *)
let lookup_field : type n. n t -> n index -> string -> string list option =
 fun { ctx; used = _ } x f ->
  let rec lookup : type n. n ctx -> n index -> string list option =
   fun ctx x ->
    match (ctx, x) with
    | Emp, _ -> .
    | Snoc (ctx, _, _), Index (Later x, fa) -> lookup ctx (Index (x, fa))
    | Snoc (_, Variables (_, mn, _), fields), Index (Now, fa) ->
        let open Monad.Ops (Monad.Maybe) in
        let (SFace_of_plus (_, fb, fc)) = sface_of_plus mn fa in
        let* _ = is_id_sface fc in
        let* y = Abwd.find_opt f fields in
        return (cubevar y fb) in
  lookup ctx x

let rec primes n =
  if n <= 0 then ""
  else if n = 1 then "′"
  else if n = 2 then "″"
  else if n = 3 then "‴"
  else "⁗" ^ primes (n - 4)

(* Make a variable name unique, adding the new one to the list of used variables and returning it. *)
let uniquify : string -> StringSet.t -> string * [ `Original | `Renamed ] * StringSet.t =
 fun name used ->
  let rec until_unique k =
    let namek = name ^ primes k in
    if StringSet.mem namek used then until_unique (k + 1) else namek in
  let namen = until_unique 0 in
  (namen, `Renamed, used |> StringSet.add namen)

(* Create a new unique variable name, for a previously unnamed variable, from a list of possibilities.  The result is always "Renamed". *)
let new_name :
    string -> string list -> StringSet.t -> string * [ `Original | `Renamed ] * StringSet.t =
 fun face names used ->
  let rec go n = function
    | [] -> go (n + 1) names
    | name :: rest ->
        let namen = name ^ face ^ primes n in
        if StringSet.mem namen used then go n rest
        else (namen, `Renamed, used |> StringSet.add namen) in
  go 0 names

(* Make a variable name or placeholder unique.  Leave placeholders as-is, unless force_names = true in which case find a name for them. *)
let uniquify_opt : type a.
    (a -> string option * string) ->
    ?force_names:bool ->
    a ->
    StringSet.t ->
    string option * [ `Original | `Renamed ] * StringSet.t =
 fun f ?(force_names = false) name used ->
  match (f name, force_names) with
  | (None, _), false -> (None, `Original, used)
  | (None, face), true ->
      let name, orig, used = new_name face (Display.variables ()) used in
      (Some name, orig, used)
  | (Some name, face), _ ->
      let name, orig, used = uniquify (name ^ face) used in
      (Some name, orig, used)

(* Do the same thing to a whole cube of variable names. *)
let uniquify_cube : type n left right a.
    (a -> string option * string) ->
    ?force_names:bool ->
    (left, n, a, right) NICubeOf.t ->
    StringSet.t ->
    (left, n, string option, right) NICubeOf.t * StringSet.t =
 fun f ?(force_names = false) names used ->
  (* Apparently we need to define the iteration function with an explicit type so that it ends up sufficiently polymorphic. *)
  let uniquify_nfamof : type m left.
      (left, m, a) NFamOf.t -> StringSet.t -> (left, m, string option) NFamOf.t * StringSet.t =
   fun (NFamOf name) used ->
    let name, _, used = uniquify_opt f ~force_names name used in
    (NFamOf name, used) in
  let open NICubeOf.Applicatic (Applicative.OfMonad (Monad.State (struct
    type t = StringSet.t
  end))) in
  mapM { map = (fun _ name used -> uniquify_nfamof name used) } names used

(* Add a new cube variable at a specified dimension, generating a fresh version of its name if necessary to avoid conflicts.  Again, leave unnamed variables unnamed unless rename=true. *)
let add_cube : type n b.
    ?force_names:bool -> n D.t -> b t -> string option -> string option * (b, n) snoc t =
 fun ?(force_names = false) n { ctx; used } name ->
  let name, _, used = uniquify_opt (fun x -> (x, "")) ~force_names name used in
  ( name,
    { ctx = Snoc (ctx, Variables (n, D.plus_zero n, NICubeOf.singleton name), Abwd.empty); used } )

(* Add a cube of variables, generating a fresh version of each of their names.  Again, leave unnamed variables unnamed unless force_names=true. *)
let add : type b n. ?force_names:bool -> b t -> n variables -> n variables * (b, n) snoc t =
 fun ?(force_names = false) { ctx; used } (Variables (m, mn, names)) ->
  let names, used = uniquify_cube (fun x -> (x, "")) ~force_names names used in
  let vars = Variables (m, mn, names) in
  (vars, { ctx = Snoc (ctx, vars, Abwd.empty); used })

(* Add a partially-cube variable as a full cube of non-cube variables, with face names explicitly concatenated with the variable names, making all variables named. *)
let add_full : type b mn. b t -> mn variables -> mn variables * (b, mn) snoc t =
 fun { ctx; used } (Variables (m, m_n, xs)) ->
  let (Wrap (newxs, _)) =
    NICubeOf.NFold.build_left (D.plus_out m m_n)
      {
        build =
          (fun s i ->
            let (SFace_of_plus (_, sm, sn)) = sface_of_plus m_n s in
            let smstr = string_of_sface ~unicode:(Display.chars () = `Unicode) sm in
            Fwrap (NFamOf (NICubeOf.find xs sn, smstr), N.suc i));
      }
      N.zero in
  let names, used = uniquify_cube (fun x -> x) ~force_names:true newxs used in
  let vars = Variables (D.zero, D.zero_plus (D.plus_out m m_n), names) in
  (vars, { ctx = Snoc (ctx, vars, Abwd.empty); used })

(* Extract all the names in a context, generating a fresh version of each name from left to right, including field access variables, leaving unnamed variables unnamed. *)
let rec of_ordered_ctx : type a b. (a, b) Ctx.Ordered.t -> b t = function
  | Emp -> empty
  | Snoc (ctx, Vis { dim; plusdim; vars; bindings = _; hasfields = _; fields; fplus = _ }, _) ->
      let { ctx; used } = of_ordered_ctx ctx in
      let vars, used = uniquify_cube (fun x -> (x, "")) vars used in
      let module M = Mbwd.Monadic (Monad.State (struct
        type t = StringSet.t
      end)) in
      let fields, used =
        M.mmapM
          (fun [ (f, x) ] used ->
            let x, _, used = uniquify x used in
            ((Field.to_string f, x), used))
          [ Bwv.to_bwd fields ]
          used in
      { ctx = Snoc (ctx, Variables (dim, plusdim, vars), fields); used }
  | Snoc (ctx, Invis bindings, _) -> snd (add_cube (CubeOf.dim bindings) (of_ordered_ctx ctx) None)
  | Lock ctx -> of_ordered_ctx ctx

let of_ctx : type a b. (a, b) Ctx.t -> b t = function
  | Permute { ctx; _ } -> of_ordered_ctx ctx

(* Add a cube of variables WITHOUT replacing them by fresh versions.  Should only be used when the variables have already been so replaced, as in the output of uniquify_vars below. *)
let unsafe_add : 'b t -> 'n variables -> (string, string) Abwd.t -> ('b, 'n) snoc t =
 fun { ctx; used } vars fields -> { ctx = Snoc (ctx, vars, fields); used }

(* Given a Bwv of variables, proceed through from the *right* to mark them as visible or shadowed, accumulating a list of the visible names in a map.  Missing variables are marked as shadowed. *)
let rec used_vars : type n.
    (string option, n) Bwv.t ->
    StringSet.t ->
    (string option * [ `Visible | `Shadowed ], n) Bwv.t * StringSet.t =
 fun vars used ->
  let do_var x used =
    match x with
    | Some x ->
        if StringSet.mem x used then (Some x, `Shadowed, used)
        else (Some x, `Visible, used |> StringSet.add x)
    | None -> (None, `Shadowed, used) in
  match vars with
  | Emp -> (Emp, used)
  | Snoc (vars, x) ->
      let x, o, used = do_var x used in
      let vars, used = used_vars vars used in
      (Snoc (vars, (x, o)), used)

(* Uniquify the names in a bwv from the *right*, thus leaving unchanged those that are still in lexical scope.  Also assigns an autogenerated name to previously unnamed variables.  Returns a Names object in the empty context that can then be used to build up a new one including those variables.  Since those variables have already been uniquified, they should be added in with unsafe_add.  (TODO: Can we avoid having to expose unsafe_add?) *)
let uniquify_vars : type a.
    (string option, a) Bwv.t -> (string * [ `Original | `Renamed ], a) Bwv.t * emp t =
 fun vars ->
  (* First we collect a map of all the visible names, also marking the given names as visible or shadowed. *)
  let vars, used = used_vars vars StringSet.empty in
  (* Then we proceed again from right to left, leaving the visible variables alone and replacing the shadowed ones with uniquified versions.  We do this in two passes to ensure that the uniquified version of a shadowed variable is never chosen in such a way as would shadow a variable to its left that already had that name. *)
  let rec go : type n.
      (string option * [ `Visible | `Shadowed ], n) Bwv.t ->
      StringSet.t ->
      (string * [ `Original | `Renamed ], n) Bwv.t * StringSet.t =
   fun vars used ->
    match vars with
    | Emp -> (Emp, used)
    | Snoc (vars, (x, sh)) ->
        let x, orig, used =
          match sh with
          | `Visible -> (x, `Original, used)
          | `Shadowed ->
              let x, _, used = uniquify_opt (fun x -> (x, "")) ~force_names:true x used in
              (x, `Renamed, used) in
        let vars, used = go vars used in
        (Snoc (vars, (Option.get x, orig)), used) in
  let vars, used = go vars used in
  (vars, { ctx = Emp; used })

type named_term = Named : 'a t * ('a, kinetic) term -> named_term
