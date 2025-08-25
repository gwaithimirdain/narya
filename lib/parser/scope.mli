open Util
open Core
open Origin
module Trie = Yuujinchou.Trie

module Param : sig
  type data =
    [ `Constant of Constant.t | `Notation of User.prenotation * User.notation ]
    * Asai.Range.t option

  type tag = unit
  type hook = unit
  type context = unit
end

module Mod : sig
  include module type of Yuujinchou.Modifier.Make (Param)

  val union :
    ?prefix:Trie.bwd_path ->
    ?context:Param.context ->
    (Param.data, Param.tag) Trie.t ->
    (Param.data, Param.tag) Trie.t ->
    (Param.data, Param.tag) Trie.t

  val union_subtree :
    ?prefix:Trie.bwd_path ->
    ?context:Param.context ->
    (Param.data, Param.tag) Trie.t ->
    Trie.path * (Param.data, Param.tag) Trie.t ->
    (Param.data, Param.tag) Trie.t

  val union_singleton :
    ?prefix:Trie.bwd_path ->
    ?context:Param.context ->
    (Param.data, Param.tag) Trie.t ->
    Trie.path * (Param.data * Param.tag) ->
    (Param.data, Param.tag) Trie.t

  val union_root :
    ?prefix:Trie.bwd_path ->
    ?context:Param.context ->
    (Param.data, Param.tag) Trie.t ->
    Param.data * Param.tag ->
    (Param.data, Param.tag) Trie.t
end

type trie = (Param.data, Param.tag) Trie.t
type t

val set_default : trie -> unit
val resolve : Trie.path -> (Param.data * Param.tag) option
val modify_export : ?context_export:Param.context -> Param.hook Yuujinchou.Language.t -> unit

val export_visible :
  ?context_modifier:Param.context ->
  ?context_export:Param.context ->
  Param.hook Yuujinchou.Language.t ->
  unit

val include_subtree :
  ?context_modifier:Param.context ->
  ?context_visible:Param.context ->
  ?context_export:Param.context ->
  ?modifier:Param.hook Yuujinchou.Language.t ->
  Trie.path * (Param.data, Param.tag) Trie.t ->
  unit

val import_subtree :
  ?context_modifier:Param.context ->
  ?context_visible:Param.context ->
  ?modifier:Param.hook Yuujinchou.Language.t ->
  Trie.path * (Param.data, Param.tag) Trie.t ->
  unit

val get_visible : unit -> trie
val get_export : unit -> trie
val set_visible : trie -> unit
val start_section : string list -> unit
val end_section : unit -> string list option
val count_sections : unit -> int
val lookup : Trie.path -> Constant.t option
val find_data : ('a * 'c, 'b) Trie.t -> 'a -> Trie.path option
val name_of : Constant.t -> Trie.path
val marshal_original_names : out_channel -> Marshal.extern_flags list -> unit
val define : ?loc:Asai.Range.t -> Trie.path -> Constant.t
val redefine : (Constant.t, string list) Hashtbl.t -> (File.t -> File.t) -> Constant.t -> Constant.t
val define_notation : User.prenotation -> ?loc:Asai.Range.t -> Trie.path -> User.key list
val check_name : Trie.path -> Asai.Range.t option -> unit

module Situation : sig
  val get : unit -> Situation.t
  val left_closeds_at : Origin.t -> (No.plus_omega, No.strict) Notation.entry
  val left_closeds : unit -> (No.plus_omega, No.strict) Notation.entry
  val tighters_at : Origin.t -> ('tight, 'strict) No.iinterval -> ('tight, 'strict) Notation.entry
  val tighters : ('tight, 'strict) No.iinterval -> ('tight, 'strict) Notation.entry
  val left_opens_at : Origin.t -> Token.t -> No.interval option
  val left_opens : Token.t -> No.interval option
  val unparse : Situation.PrintKey.t -> User.notation option
  val add : ('left, 'tight, 'right) Notation.notation -> unit
  val add_user : User.prenotation -> User.notation * User.key list
end
