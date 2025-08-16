(* Applicative (i.e. lax monoidal) functors.  This module is not meant to be opened; its sub-modules should be used qualified. *)

module type Plain = sig
  type 'a t

  val return : 'a -> 'a t
  val apply : 'a t -> ('a -> 'b) -> 'b t

  (* We wrap the arguments of zip in thunks, so that in OfMonad we can wait to evaluate the second argument inside the binder function of the monad.  Unfortunately, that means we can't use OCaml's nice syntax like "let+" and "and+" for applicatives. *)
  val zip : (unit -> 'a t) -> (unit -> 'b t) -> ('a * 'b) t
end

module Ops (M : Plain) = struct
  let return = M.return
end

(* Every (strong) monad is an applicative functor. *)

module OfMonad (M : Monad.Plain) = struct
  type 'a t = 'a M.t

  let return x = M.return x
  let apply mx f = M.bind mx (fun x -> return (f x))

  (* By not forcing the thunk my until inside the binder function, we recover more faithful monadic behavior.  For instance, in an Error or Maybe monad, if mx errors then this way, then my will not be evaluated at all; whereas with a naive "unthunked" definition of zip, it would still be.  (Perhaps the latter is what most people intend with Applicative functors, but it's not what we want.) *)
  let zip mx my = M.bind (mx ()) (fun x -> M.bind (my ()) (fun y -> M.return (x, y)))
end

(* Streams are an applicative functor (Haskell's "ZipList"), but not a monad. *)

module Stream = struct
  type 'a t = Cons of ('a * 'a t) Lazy.t

  let rec return : type a. a -> a t = fun x -> Cons (lazy (x, return x))

  let rec apply : type a b. a t -> (a -> b) -> b t =
   fun xs f ->
    Cons
      (lazy
        (let (Cons (lazy (x, xs))) = xs in
         (f x, apply xs f)))

  let rec zip : type a b. (unit -> a t) -> (unit -> b t) -> (a * b) t =
   fun xs ys ->
    Cons
      (lazy
        (let (Cons (lazy (x, xs))) = xs () in
         let (Cons (lazy (y, ys))) = ys () in
         ((x, y), zip (fun () -> xs) (fun () -> ys))))
end

(* The "reverse state" effect threads state (and execution order) from right to left, rather than left to right as usual.  It is apparently possible to actually make this a monad in Haskell with laziness, and possibly even in OCaml with Lazy.t, but when I tried that I couldn't get it to work.  Fortunately it is much easier as an applicative functor. *)

module type State_type = sig
  type t
end

module RevState (S : State_type) = struct
  type 'a t = S.t -> 'a * S.t

  let return (x : 'a) : 'a t = fun s -> (x, s)

  let apply : type a b. a t -> (a -> b) -> b t =
   fun mx f s1 ->
    let x, s2 = mx s1 in
    (f x, s2)

  let zip : type a b. (unit -> a t) -> (unit -> b t) -> (a * b) t =
   fun xs ys s1 ->
    (* Here's the reversal: we evaluate ys first and pass its output state "back" to xs. *)
    let y, s2 = ys () s1 in
    let x, s3 = xs () s2 in
    ((x, y), s3)

  let get : S.t t = fun s -> (s, s)
  let modify : (S.t -> S.t) -> unit t = fun f s -> ((), f s)
  let put : S.t -> unit t = fun s -> modify (fun _ -> s)
end

(* The "reversal" aspect can be separated out into a transformer that acts on any applicative functor. *)

module ReverseT (M : Plain) = struct
  type 'a t = 'a M.t

  let return x = M.return x
  let apply x f = M.apply x f

  let zip mx my =
    let open Ops (M) in
    M.apply (M.zip my mx) @@ fun (y, x) -> (x, y)
end
