(* Check that a mode theory's find_unique, which decides whether there is a cell between two modalities, is closed under the operations that generate 2-cells, on all modalities up to a given length: it must contain the generating 2-cells and identities, and be closed under vertical composition and whiskering by generators.  If it is, it contains every 2-cell derivable without passing through a longer modality.  Run with the name of a mode theory and a maximum length. *)

open Modal

type word = W : ('a, 'm, 'b) Modality.t -> word

let install = function
  | "trivial" -> Trivial.install [] [] []
  | "functor" -> Functor.install (module Functor.Ordinary : Functor.Variant) [] [] []
  | "composable-functors" -> Composable_functors.install [] [] []
  | "transformation" -> Transformation.install [] [] []
  | "composable-transformations" -> Composable_transformations.install [] [] []
  | "interchange" -> Interchange.install [] [] []
  | "reflector" -> Reflector.install [] [] []
  | "coreflector" ->
      Coreflector.install (module Coreflector.Ordinary : Coreflector.Variant) [] [] []
  | "coreflection" ->
      Coreflection.install (module Coreflection.Ordinary : Coreflection.Variant) [] [] []
  | "guarded" -> Guarded.install [] [] []
  | "local" -> Local.install (module Local.Ordinary : Local.Variant) [] [] []
  | "tconn" -> Tconn.install (module Tconn.Ordinary : Tconn.Variant) [] [] []
  | "spatial" -> Spatial.install (module Spatial.Ordinary : Spatial.Variant) [] [] []
  | "cospatial" -> Cospatial.install (module Cospatial.Ordinary : Cospatial.Variant) [] [] []
  | "ambiflection" ->
      Ambiflection.install (module Ambiflection.Ordinary : Ambiflection.Variant) [] [] []
  | "ambiflector" ->
      Ambiflector.install (module Ambiflector.Ordinary : Ambiflector.Variant) [] [] []
  | t -> failwith ("unknown theory " ^ t)

let loc x = Asai.Range.locate_opt None x

let key (W w) =
  String.concat " " (Mode.name (Modality.src w) :: Mode.name (Modality.tgt w) :: Modality.name w)

let () =
  let theory = Sys.argv.(1) in
  let maxlen = int_of_string Sys.argv.(2) in
  install theory;
  let modes = Mode.all () in
  let gens =
    List.concat_map
      (fun (_, Mode.Wrap m) ->
        List.filter_map
          (fun g ->
            match Modality.of_name_src [ loc g ] m with
            | Ok (Wrap t) -> Some (W t)
            | Error _ -> None)
          (Modality.all_names ()))
      modes in
  (* All words up to the maximum length, level by level. *)
  let compose (W x) (W g) =
    match Mode.compare (Modality.src g) (Modality.tgt x) with
    | Eq ->
        let (Comp c) = Modality.comp x in
        Some (W (Modality.comp_out g c))
    | Neq -> None in
  let rec levels n prev acc =
    if n >= maxlen then acc
    else
      let next = List.concat_map (fun w -> List.filter_map (fun g -> compose w g) gens) prev in
      levels (n + 1) next (acc @ next) in
  let ids = List.map (fun (_, Mode.Wrap m) -> W (Modality.id m)) modes in
  let words = Array.of_list (levels 0 ids ids) in
  let index = Hashtbl.create 100 in
  Array.iteri (fun i w -> Hashtbl.replace index (key w) i) words;
  let n = Array.length words in
  let same_hom (W x) (W y) =
    match
      ( Mode.compare (Modality.src x) (Modality.src y),
        Mode.compare (Modality.tgt x) (Modality.tgt y) )
    with
    | Eq, Eq -> true
    | _ -> false in
  let decide (W x) (W y) =
    match Modalcell.find_unique x y with
    | Some _ -> true
    | None -> false
    | exception e ->
        Printf.printf "exception on %s => %s: %s\n" (key (W x)) (key (W y)) (Printexc.to_string e);
        false in
  let d = Array.make_matrix n n false in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if same_hom words.(i) words.(j) then d.(i).(j) <- decide words.(i) words.(j)
    done
  done;
  let violations = ref 0 in
  let report what i j =
    incr violations;
    if !violations <= 20 then
      Printf.printf "missing (%s): %s  =>  %s\n" what (key words.(i)) (key words.(j)) in
  (* Identities. *)
  for i = 0 to n - 1 do
    if not d.(i).(i) then report "identity" i i
  done;
  (* Generating cells. *)
  List.iter
    (fun (_, Mode.Wrap m) ->
      List.iter
        (fun c ->
          match Modalcell.of_name m (loc [ c ]) with
          | Ok (Wrap cell) -> (
              let s = key (W (Modalcell.vsrc cell)) and t = key (W (Modalcell.vtgt cell)) in
              match (Hashtbl.find_opt index s, Hashtbl.find_opt index t) with
              | Some i, Some j -> if not d.(i).(j) then report ("generator " ^ c) i j
              | _ -> ())
          | Error _ -> ())
        (Modalcell.all_names ()))
    modes;
  (* Vertical composition. *)
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if d.(i).(j) then
        for k = 0 to n - 1 do
          if d.(j).(k) && not d.(i).(k) then report "composite" i k
        done
    done
  done;
  (* Whiskering by generators on either side. *)
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if d.(i).(j) then
        List.iter
          (fun g ->
            (match (compose words.(i) g, compose words.(j) g) with
            | Some x, Some y -> (
                match (Hashtbl.find_opt index (key x), Hashtbl.find_opt index (key y)) with
                | Some i', Some j' -> if not d.(i').(j') then report "postwhisker" i' j'
                | _ -> ())
            | _ -> ());
            match (compose g words.(i), compose g words.(j)) with
            | Some x, Some y -> (
                match (Hashtbl.find_opt index (key x), Hashtbl.find_opt index (key y)) with
                | Some i', Some j' -> if not d.(i').(j') then report "prewhisker" i' j'
                | _ -> ())
            | _ -> ())
          gens
    done
  done;
  let cells =
    Array.fold_left (fun acc row -> Array.fold_left (fun a b -> if b then a + 1 else a) acc row) 0 d
  in
  Printf.printf "%s: %d words up to length %d, %d cells, %d violations\n" theory n maxlen cells
    !violations
