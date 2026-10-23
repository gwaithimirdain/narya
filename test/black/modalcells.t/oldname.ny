def □△ (A : Disc) : Disc ≔ data [ □△. (_ :□△| A) ]
def □△□△ (A : Disc) : Disc ≔ data [ □△□△. (_ :□△□△| A) ]

` After renaming, the old default name "η" for the unit cell is unknown.
def needs_key (A : Disc) (x :□△| A) : □△□△ A ≔ □△□△. (x #η)
