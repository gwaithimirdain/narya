import "equational"
def unicode : Id A y z ≔ calc y = z by {` before `} ← {` after `} s ∎
def ascii : Id A y z ≔ calc y = z by <-s ∎
