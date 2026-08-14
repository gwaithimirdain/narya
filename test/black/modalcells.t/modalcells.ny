option modal ≔ adjunction, modalcells myeta myeps

def □△ (A : Disc) : Disc ≔ data [ t. (_ :□△| A) ]
def □△□△ (A : Disc) : Disc ≔ data [ t2. (_ :□△□△| A) ]

` The generating unit 2-cell of the adjunction, renamed to "myeta" via -modalcells.
def needs_key (A : Disc) (x :□△| A) : □△□△ A ≔ t2. (x #myeta)
