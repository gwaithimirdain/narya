type (_, _) t = Eq : ('a, 'a) t
type (_, _) compare = Eq : ('a, 'a) compare | Neq : ('a, 'b) compare
type ('a, 'b) neq = { abort : 'r. ('a, 'b) t -> 'r }
