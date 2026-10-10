def N : Type ≔ data [ zero. | suc. (_ : N) ]

def Bool : Type ≔ data [ true. | false. ]

def √N : Type ≔ codata [ x .root.e : N ]

axiom f : N → √N
