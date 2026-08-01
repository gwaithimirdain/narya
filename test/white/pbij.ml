(* Test that [plus_comp_pbij] agrees with an independent model of partial bijection composition.

   A partial bijection ('e,'i,'r) pbij is equivalent to its "total insertion" ('r+'e, 'res, 'i), obtained by adjoining the remaining dimension on the left of the evaluation dimension, and hence to the permutation ('r+'e) -> ('res+'i) that this insertion induces.  Composing partial bijections should correspond to composing those permutations:

     r12 + e1 + e2  --(p1 * id)-->  res1 + r2 + e2  --(id * p2)-->  res1 + res2 + i

   so we check that against the permutation induced by [plus_comp_pbij]. *)

open Dim

let dim : int -> D.wrapped =
 fun n ->
  let rec go n =
    if n <= 0 then D.Wrap D.zero
    else
      let (D.Wrap m) = go (n - 1) in
      let (D.Plus p) = D.plus D.one in
      D.Wrap (D.plus_out m p) in
  go n

let check : type e1 e2 e12 i r2 r12.
    (e1, e2, e12) D.plus -> (e2, i, r2) pbij -> (e1, r2, r12) pbij -> bool =
 fun e1e2 p2 p1 ->
  let (Pbij (ins1, shuf1)) = p1 in
  let (Pbij (ins2, shuf2)) = p2 in
  let p12 = plus_comp_pbij e1e2 p2 p1 in
  let (Pbij (ins12, shuf12)) = p12 in
  let e2dim = D.plus_right e1e2 in
  (* p1 induces a degeneracy (r12+e1) -> (res1+r2). *)
  let (D.Plus r12e1) = D.plus (dom_pbij p1) in
  let tins1 = ins_plus_of_pbij ins1 shuf1 r12e1 in
  let res1 = cod_left_ins tins1 in
  let (D.Plus res1r2) = D.plus (cod_pbij p1) in
  let deg1 = deg_of_ins_plus tins1 res1r2 in
  (* p2 induces a degeneracy (r2+e2) -> (res2+i). *)
  let (D.Plus r2e2) = D.plus (dom_pbij p2) in
  let tins2 = ins_plus_of_pbij ins2 shuf2 r2e2 in
  let (D.Plus res2i) = D.plus (cod_pbij p2) in
  let deg2 = deg_of_ins_plus tins2 res2i in
  let res2idim = D.plus_out (cod_left_ins tins2) res2i in
  (* Whisker the first with e2 on the right: (r12+e1)+e2 -> (res1+r2)+e2. *)
  let (D.Plus res1r2_e2) = D.plus e2dim in
  let (D.Plus r12e1_e2) = D.plus e2dim in
  let first = deg_plus_deg deg1 res1r2_e2 r12e1_e2 (id_deg e2dim) in
  (* Whisker the second with res1 on the left: res1+(r2+e2) -> res1+(res2+i). *)
  let res1_r2e2 = D.plus_assocr res1r2 r2e2 res1r2_e2 in
  let (D.Plus res1_res2i) = D.plus res2idim in
  let second = deg_plus_deg (id_deg res1) res1_res2i res1_r2e2 deg2 in
  let expected = comp_deg second first in
  (* And compare with the degeneracy induced by the composite, whose domain r12+(e1+e2) is the same as (r12+e1)+e2. *)
  let r12_e12 = D.plus_assocr r12e1 e1e2 r12e1_e2 in
  let tins12 = ins_plus_of_pbij ins12 shuf12 r12_e12 in
  let (D.Plus res12i) = D.plus (cod_pbij p12) in
  let actual = deg_of_ins_plus tins12 res12i in
  match (D.compare (cod_deg expected) (cod_deg actual), deg_equiv expected actual) with
  | Eq, Some () -> true
  | _ ->
      Printf.printf "  expected %s, got %s\n" (string_of_deg expected) (string_of_deg actual);
      false

let () =
  let dims = List.init 4 dim in
  let count = ref 0 in
  let bad = ref 0 in
  List.iter
    (fun (D.Wrap e1) ->
      List.iter
        (fun (D.Wrap e2) ->
          List.iter
            (fun (D.Wrap i) ->
              let (D.Plus e1e2) = D.plus e2 in
              Seq.iter
                (fun (Pbij_between p2) ->
                  Seq.iter
                    (fun (Pbij_between p1) ->
                      incr count;
                      if not (check e1e2 p2 p1) then (
                        incr bad;
                        Printf.printf "FAIL e1=%s e2=%s i=%s: p2=%s p1=%s gave %s\n"
                          (string_of_dim e1) (string_of_dim e2) (string_of_dim i)
                          (string_of_pbij p2) (string_of_pbij p1)
                          (string_of_pbij (plus_comp_pbij e1e2 p2 p1))))
                    (all_pbij_between e1 (remaining p2)))
                (all_pbij_between e2 i))
            dims)
        dims)
    dims;
  Printf.printf "checked %d compositions, %d failures\n" !count !bad
