(* Check that a mode theory's decision of whether there is a cell between two modalities (by find_all, or find_unique if it can't enumerate them) is closed under the operations that generate 2-cells, on all modalities up to a given length: it must contain the generating 2-cells and identities, and be closed under vertical composition and whiskering by generators.  If it is, it contains every 2-cell derivable without passing through a longer modality.  Run with the name of a mode theory and a maximum length. *)

open Modal

type word = W : ('a, 'm, 'b) Modality.t -> word
type any_cell = Cell : ('a, 'm, 'n, 'b) Modalcell.t -> any_cell

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
  | "adjunction" -> Adjunction.install (module Adjunction.Ordinary : Adjunction.Variant) [] [] []
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
  (* Whether there is a cell: some cell, if the theory can enumerate them, and otherwise a unique one. *)
  let decide (W x) (W y) =
    match Modalcell.find_all x y with
    | Some (All (_ :: _)) -> true
    | Some (All []) | Some Incompatible -> false
    | None -> Option.is_some (Modalcell.find_unique x y)
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
  (* If the theory enumerates the cells, its lists must contain each derivable cell exactly once: they must have no repetitions, and contain the identities and generating cells and be closed under vertical composition and whiskering by generators, up to equality of cells. *)
  let lists = Array.make_matrix n n None in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if same_hom words.(i) words.(j) then
        let W x, W y = (words.(i), words.(j)) in
        lists.(i).(j) <-
          (match Modalcell.find_all x y with
          | Some (All l) -> Some (List.map (fun c -> Cell c) l)
          | Some Incompatible -> Some []
          | None -> None
          | exception _ -> None)
    done
  done;
  let equal (Cell c) (Cell d) =
    match Modalcell.compare c d with
    | Eq -> true
    | Neq -> false in
  let report_cell what i j =
    incr violations;
    if !violations <= 20 then
      Printf.printf "unlisted (%s): %s  =>  %s
" what (key words.(i)) (key words.(j)) in
  let listed what i j c =
    match lists.(i).(j) with
    | Some l -> if not (List.exists (equal c) l) then report_cell what i j
    | None -> () in
  let index_of (W w) = Hashtbl.find_opt index (key (W w)) in
  let rec repeated = function
    | [] -> false
    | c :: l -> List.exists (equal c) l || repeated l in
  let enumerated = ref 0 in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      match lists.(i).(j) with
      | Some l ->
          enumerated := !enumerated + List.length l;
          if repeated l then (
            incr violations;
            Printf.printf "repeated: %s  =>  %s
" (key words.(i)) (key words.(j)))
      | None -> ()
    done
  done;
  (* And find_unique must only find a cell if it is the only one. *)
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      match lists.(i).(j) with
      | Some l -> (
          let W x, W y = (words.(i), words.(j)) in
          match Modalcell.find_unique x y with
          | Some (Unique c) -> (
              match l with
              | [ d ] when equal (Cell c) d -> ()
              | _ ->
                  incr violations;
                  Printf.printf "not unique: %s  =>  %s\n" (key words.(i)) (key words.(j)))
          | None -> ())
      | None -> ()
    done
  done;
  for i = 0 to n - 1 do
    let (W x) = words.(i) in
    listed "identity" i i (Cell (Modalcell.id x))
  done;
  List.iter
    (fun (_, Mode.Wrap m) ->
      List.iter
        (fun c ->
          match Modalcell.of_name m (loc [ c ]) with
          | Ok (Wrap cell) -> (
              match (index_of (W (Modalcell.vsrc cell)), index_of (W (Modalcell.vtgt cell))) with
              | Some i, Some j -> listed ("generator " ^ c) i j (Cell cell)
              | _ -> ())
          | Error _ -> ())
        (Modalcell.all_names ()))
    modes;
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      match lists.(i).(j) with
      | Some l1 ->
          for k = 0 to n - 1 do
            match lists.(j).(k) with
            | Some l2 ->
                List.iter
                  (fun (Cell c1) ->
                    List.iter
                      (fun (Cell c2) ->
                        match Modality.compare (Modalcell.vtgt c1) (Modalcell.vsrc c2) with
                        | Eq -> listed "composite" i k (Cell (Modalcell.vcomp c2 c1))
                        | Neq -> ())
                      l2)
                  l1
            | None -> ()
          done
      | None -> ()
    done
  done;
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      match lists.(i).(j) with
      | Some l ->
          List.iter
            (fun (Cell c) ->
              List.iter
                (fun (W g) ->
                  (match Mode.compare (Modality.src g) (Modalcell.htgt c) with
                  | Eq -> (
                      let (Wrap c') = Modalcell.postwhisker_wrapped g c in
                      match
                        (index_of (W (Modalcell.vsrc c')), index_of (W (Modalcell.vtgt c')))
                      with
                      | Some i', Some j' -> listed "postwhisker" i' j' (Cell c')
                      | _ -> ())
                  | Neq -> ());
                  match Mode.compare (Modality.tgt g) (Modalcell.hsrc c) with
                  | Eq -> (
                      let (Wrap c') = Modalcell.prewhisker_wrapped c g in
                      match
                        (index_of (W (Modalcell.vsrc c')), index_of (W (Modalcell.vtgt c')))
                      with
                      | Some i', Some j' -> listed "prewhisker" i' j' (Cell c')
                      | _ -> ())
                  | Neq -> ())
                gens)
            l
      | None -> ()
    done
  done;
  let cells =
    Array.fold_left (fun acc row -> Array.fold_left (fun a b -> if b then a + 1 else a) acc row) 0 d
  in
  if !enumerated > 0 then Printf.printf "%s: %d cells enumerated\n" theory !enumerated;
  Printf.printf "%s: %d words up to length %d, %d cells, %d violations\n" theory n maxlen cells
    !violations
