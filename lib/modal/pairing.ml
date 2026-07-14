(* Pairings of the generators occurring in the domain and codomain words of a 2-cell.  In the mode theories that are not locally posetal (-adjunction and -gwpt), a 2-cell is uniquely determined by the perfect matching ("pairing") that it induces on the generators occurring in its domain and codomain words: each generator is paired with exactly one other generator, either in the other word (a strand passing straight through) or in the same word (a strand that turns back, created by a unit or killed by a counit).  This module supplies the representation and composition of such pairings; the theory-specific part -- the pairing induced by each generating 2-cell -- lives in the individual mode theories. *)

(* An endpoint of a strand: a generator of the domain or the codomain word, numbered in application order starting from 0. *)
type endpoint = Dom of int | Cod of int

module EndpointMap = Map.Make (struct
  type t = endpoint

  let compare = (Stdlib.compare : endpoint -> endpoint -> int)
end)

type t = endpoint EndpointMap.t

(* A pairing is stored as its graph: an involutive map on endpoints. *)
let add_pair map (p, q) = EndpointMap.add p q (EndpointMap.add q p map)
let of_pairs ps = List.fold_left add_pair EndpointMap.empty ps
let equal : t -> t -> bool = EndpointMap.equal (fun (p : endpoint) q -> p = q)

(* Vertical composition of pairings follows the strings through the middle word: px is the pairing of a cell m ⇒ n and py that of a cell n ⇒ r, so the Cod endpoints of px and the Dom endpoints of py both refer to the middle word n, of length mid.  Each strand of the composite starts at an outer endpoint (a Dom of px or a Cod of py) and alternately applies px and py until it emerges at another outer endpoint.  A closed loop contained entirely in the middle word arises exactly when an invertible generating 2-cell cancels its formal inverse; it contributes nothing to the composite pairing, so if the theory has invertible units or counits (allow_loops) we drop it, and otherwise (the walking adjunction, where loops are provably impossible) we raise an exception. *)
let compose ~allow_loops mid px py =
  let mx = of_pairs px in
  let my = of_pairs py in
  let seen = Array.make mid false in
  let rec follow_x e =
    match EndpointMap.find e mx with
    | Dom i -> Dom i
    | Cod i ->
        seen.(i) <- true;
        follow_y (Dom i)
  and follow_y e =
    match EndpointMap.find e my with
    | Cod i -> Cod i
    | Dom i ->
        seen.(i) <- true;
        follow_x (Cod i) in
  let result = ref [] in
  let paired = ref EndpointMap.empty in
  let start follow e =
    if not (EndpointMap.mem e !paired) then begin
      let p = follow e in
      paired := add_pair !paired (e, p);
      result := (e, p) :: !result
    end in
  List.iter
    (fun (p, q) ->
      List.iter
        (function
          | Dom i -> start follow_x (Dom i)
          | Cod _ -> ())
        [ p; q ])
    px;
  List.iter
    (fun (p, q) ->
      List.iter
        (function
          | Cod j -> start follow_y (Cod j)
          | Dom _ -> ())
        [ p; q ])
    py;
  if (not allow_loops) && not (Array.for_all Fun.id seen) then
    failwith "closed loop in composite 2-cell (should be impossible)";
  List.rev !result

(* Since parallel 2-cells can differ, a cell is displayed by its pairing. *)
let to_string ps =
  let endpoint_str = function
    | Dom i -> "d" ^ string_of_int i
    | Cod i -> "c" ^ string_of_int i in
  let ps = List.map (fun (p, q) -> if p <= q then (p, q) else (q, p)) ps in
  "cell("
  ^ String.concat ","
      (List.map (fun (p, q) -> endpoint_str p ^ endpoint_str q) (List.sort Stdlib.compare ps))
  ^ ")"
