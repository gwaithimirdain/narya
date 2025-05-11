open Bwd
open Dim
open Util
open Signatures

type raw = string * int Bwd.t
type 'i field
type 'i t = 'i field

val intern : string -> 'i D.t -> 'i t
val to_string : 'i t -> string
val strings_to_string : string -> string list -> string
val dim : 'i t -> 'i D.t
val equal : 'i t -> 'j t -> ('i, 'j) Eq.compare

type wrapped = Wrap : 'i t -> wrapped
type with_ins = WithIns : 'i t * ('n, 't, 'i) insertion -> with_ins
type or_index = Name : raw -> or_index | Index : int -> or_index

val to_string_ori : or_index -> string
val intern_ori : string -> or_index

module Abwd : functor (F : Fam2) -> sig
  type 'a entry = Entry : ('i t * ('i, 'a) F.t) -> 'a entry
  type 'a t = 'a entry Bwd.t

  type (_, _) find_opt_result =
    | Found : ('i, 'a) F.t -> ('i, 'a) find_opt_result
    | Wrong_dimension : 'j D.t * ('j, 'a) F.t -> ('i, 'a) find_opt_result
    | Not_found : ('i, 'a) find_opt_result

  val find_opt : 'a t -> 'i field -> ('i, 'a) find_opt_result
  val find_string_opt : 'a t -> string -> 'a entry option
end
