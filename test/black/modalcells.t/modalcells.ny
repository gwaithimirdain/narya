def □△ (A : Disc) : Disc ≔ data [ □△. (_ :□△| A) ]
def □△□△ (A : Disc) : Disc ≔ data [ □△□△. (_ :□△□△| A) ]

` The generating unit 2-cell of the adjunction, renamed to "myeta" via -modalcells.
def needs_key (A : Disc) (x :□△| A) : □△□△ A ≔ □△□△. (x #myeta)
