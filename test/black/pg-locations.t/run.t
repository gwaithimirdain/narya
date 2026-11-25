In ProofGeneral mode, solving a hole with a tuple whose last field is labeled reports the new holes' offsets relative to the start of the whole term, and an error in such a tuple is located on the whole tuple.

  $ printf 'axiom A : Type\n\f\ndef AB : Type := sig ( fst : A, snd : A )\n\f\ndef x : AB := ?\n\f\nsolve 0 0 := (fst := ?, snd := ?)\n\f\ndef y : A := (fst := A, snd := A)\n\f\n' | narya -proofgeneral | sed -n -e '/\[data\]/,/\[reformat\]/p' -e '/\[errors\]/,/\[narya\]/p'
  [data]
  unparenthesized
  1
  [reformat]
  [data]
  unparenthesized
  2
  [reformat]
  [data]
  unparenthesized
  3
  0 14 15
  [reformat]
  [data]
  unparenthesized
  3
  1 8 9
  2 18 19
  [reformat]
  [errors]
  13 33
  [narya]
