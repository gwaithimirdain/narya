open Util
open Core
open Origin
open Parser

let marshal chan isfibrant_file fibrancy_file =
  Marshal.to_channel chan isfibrant_file [];
  Marshal.to_channel chan fibrancy_file [];
  Global.to_channel_origin chan Top [];
  Global.to_channel_origin chan (File isfibrant_file) [];
  Global.to_channel_origin chan (File fibrancy_file) [];
  Marshal.to_channel chan !Fibrancy.fields [];
  Marshal.to_channel chan !Fibrancy.pi [];
  Marshal.to_channel chan !Fibrancy.glue [];
  Scope.to_channel chan (Scope.get_visible ()) []

let unmarshal chan =
  let old_isfibrant_file = (Istream.unmarshal chan : File.t) in
  let old_fibrancy_file = (Istream.unmarshal chan : File.t) in
  let new_isfibrant_file = File.make (`Other "isfibrant bootstrap") in
  let new_fibrancy_file = File.make (`Other "fibrancy bootstrap") in
  let f x =
    if x = old_isfibrant_file then new_isfibrant_file
    else if x = old_fibrancy_file then new_fibrancy_file
    else x in
  let _ = Global.from_istream_origin f chan Top in
  let _ = Global.from_istream_origin f chan (File new_isfibrant_file) in
  let _ = Global.from_istream_origin f chan (File new_fibrancy_file) in
  Fibrancy.fields := Istream.unmarshal chan;
  Fibrancy.pi := Istream.unmarshal chan;
  Fibrancy.glue := Istream.unmarshal chan;
  let trie = Scope.from_istream chan f in
  Scope.include_subtree ([], trie);
  Scope.set_default trie
