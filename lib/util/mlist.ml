(* This is just a demonstration, in the simple case of lists, of a technique for unifying tranversals of data structures.  We use it later in more complicated cases of Bwvs, Cubes, and Tubes. *)

open Effect
open Effect.Deep
open Tlist
open Hlist

module Heter = struct
  (* An hlist of lists *)
  type _ ht = [] : nil ht | ( :: ) : 'x list * 'xs ht -> ('x, 'xs) cons ht

  (* The hlist consisting of all empty lists  *)
  let rec empty : type xs. xs Tlist.t -> xs ht = function
    | Nil -> []
    | Cons xs -> [] :: empty xs

  (* Add an element to the front of each one of an hlist of lists *)
  let rec cons : type xs. xs hlist -> xs ht -> xs ht =
   fun x xs ->
    match (x, xs) with
    | [], [] -> []
    | x :: xs, y :: ys -> (x :: y) :: cons xs ys

  (* Extract the head and tail of element of every one of an hlist of lists *)

  let rec hd : type xs. xs ht -> xs hlist = function
    | [] -> []
    | x :: xs -> List.hd x :: hd xs

  let rec tl : type xs. xs ht -> xs ht = function
    | [] -> []
    | x :: xs -> List.tl x :: tl xs

  (* Every hlist of lists has a valid type *)
  let rec tlist : type xs. xs ht -> xs Tlist.t = function
    | [] -> Nil
    | _ :: xs -> Cons (tlist xs)
end

(* Now we define a single traversal function which encapsulates map, map2, map3, ..., iter, iter2, ... and also multiple-output versions.  *)

let rec pmap : type x xs ys.
    ((x, xs) cons hlist -> ys hlist) -> (x, xs) cons Heter.ht -> ys Tlist.t -> ys Heter.ht =
 fun f xss ys ->
  match xss with
  | [] :: _ -> Heter.empty ys
  | (x :: xs) :: xss ->
      let fx = f (x :: Heter.hd xss) in
      let fxs = pmap f (xs :: Heter.tl xss) ys in
      Heter.cons fx fxs

(* Since "nil hlist" is isomorphic to unit, this includes iterations, but it's more convenient to write those actually using unit. *)
let miter : type x xs. ((x, xs) cons hlist -> unit) -> (x, xs) cons Heter.ht -> unit =
 fun f xss ->
  let [] =
    pmap
      (fun x ->
        f x;
        [])
      xss Nil in
  ()

(* It's also convenient to separate out the multi-input single-output version. *)
let mmap : type x xs y. ((x, xs) cons hlist -> y) -> (x, xs) cons Heter.ht -> y list =
 fun f xs ->
  let [ ys ] = pmap (fun x -> [ f x ]) xs (Cons Nil) in
  ys

(* Ordinary ones of fixed arity are then obtained by specializing to different kinds of hlists.  Note that with hlists, the type determines how many elements it has, so a match against a list of fixed length is exhaustive.  Note that the definitions of these are so simple that the user can easily write them directly, although in some cases having the predefined wrapper speeds up compilation times. *)

let map : type x y. (x -> y) -> x list -> y list = fun f xs -> mmap (fun [ x ] -> f x) [ xs ]

let map2 : type x y z. (x -> y -> z) -> x list -> y list -> z list =
 fun f xs ys -> mmap (fun [ x; y ] -> f x y) [ xs; ys ]

let iter : type x. (x -> unit) -> x list -> unit = fun f xs -> miter (fun [ x ] -> f x) [ xs ]

let iter2 : type x y. (x -> y -> unit) -> x list -> y list -> unit =
 fun f xs ys -> miter (fun [ x; y ] -> f x y) [ xs; ys ]

(* Not only does this save copy-and-pasting, especially for data structures whose traversal is complicated to code, it also allows the user to instantiate higher-arity versions as needed by calling mmap directly.  It also includes multiple-output versions that are less commonly mentioned, with a bit of mediation between hlists and tuples: *)

let map1_2 : type x y z. (x -> y * z) -> x list -> y list * z list =
 fun f xs ->
  let [ ys; zs ] =
    pmap
      (fun [ x ] ->
        let y, z = f x in
        [ y; z ])
      [ xs ] (Cons (Cons Nil)) in
  (ys, zs)

(* In a previous version of this library we defined a version of the traversal functions parametrized over a monad, and more generally over an applicative functor.  However, it's more efficient to incorporate state and other side effects by using mutable references and algebraic effects.  For instance, a left fold is just an iteration that accumulates mutable state. *)

let mfold_left : type x xs acc.
    (acc -> (x, xs) cons hlist -> acc) -> acc -> (x, xs) cons Heter.ht -> acc =
 fun f start xss ->
  let acc = ref start in
  miter (fun xs -> acc := f !acc xs) xss;
  !acc

let fold_left : type x acc. (acc -> x -> acc) -> acc -> x list -> acc =
 fun f acc xs -> mfold_left (fun acc [ x ] -> f acc x) acc [ xs ]

let fold_left2 : type x y acc. (acc -> x -> y -> acc) -> acc -> x list -> y list -> acc =
 fun f acc xs ys -> mfold_left (fun acc [ x; y ] -> f acc x y) acc [ xs; ys ]

(* We can also transform this into a right fold by using an effect. *)

let mfold_right : type x xs acc.
    ((x, xs) cons hlist -> acc -> acc) -> (x, xs) cons Heter.ht -> acc -> acc =
 fun f xss start ->
  let acc = ref start in
  let module E = struct
    type _ Effect.t += Visit : (x, xs) cons hlist -> unit Effect.t
  end in
  (try miter (fun xs -> perform (E.Visit xs)) xss
   with effect E.Visit xs, k ->
     continue k ();
     acc := f xs !acc);
  !acc

let fold_right : type x acc. (x -> acc -> acc) -> x list -> acc -> acc =
 fun f xs acc -> mfold_right (fun [ x ] acc -> f x acc) [ xs ] acc

let fold_right2 : type x y acc. (x -> y -> acc -> acc) -> x list -> y list -> acc -> acc =
 fun f xs ys acc -> mfold_right (fun [ x; y ] acc -> f x y acc) [ xs; ys ] acc
