option modal ≔ adjunction, modalcells myeta myeps

def □△ (A : Disc) : Disc ≔ data [ t. (_ :□△| A) ]
def □△□△ (A : Disc) : Disc ≔ data [ t2. (_ :□△□△| A) ]

` After renaming, the old default name "η" for the unit cell is unknown.
def needs_key (A : Disc) (x :□△| A) : □△□△ A ≔ t2. (x #η)
