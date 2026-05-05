open Signatures
open Tlist
open Tbwd

module Make (G : Comparable) (F : Fam2) : sig
  module W : module type of Word.Make (G)

  type ('a, 'b, 'p) gt
  type ('a, 'p) t = ('a, nil, 'p) gt

  val empty : (W.zero, 'p) t
  val find : ('a, 'g, 'asuc) Tbwd.insert -> ('asuc, 'p) t -> ('a, 'p) F.t
  val set : ('a, 'g, 'asuc) Tbwd.insert -> ('a, 'p) F.t -> ('asuc, 'p) t -> ('asuc, 'p) t

  val update :
    ('a, 'g, 'asuc) Tbwd.insert -> (('a, 'p) F.t -> ('a, 'p) F.t) -> ('asuc, 'p) t -> ('asuc, 'p) t

  type ('asuc, 'p) builder = {
    build : 'a 'g. 'g G.t -> ('a, 'g, 'asuc) Tbwd.insert -> ('a, 'p) F.t;
  }

  val build : 'a W.t -> ('a, 'p) builder -> ('a, 'p) t

  module Heter : sig
    type (_, _) hft =
      | [] : ('a, nil) hft
      | ( :: ) : ('a, 'p) F.t * ('a, 'ps) hft -> ('a, ('p, 'ps) cons) hft

    type (_, _, _) hgt =
      | [] : ('a, 'b, nil) hgt
      | ( :: ) : ('a, 'b, 'p) gt * ('a, 'b, 'ps) hgt -> ('a, 'b, ('p, 'ps) cons) hgt
  end

  module Applicatic (M : Applicative.Plain) : sig
    type ('asuc, 'ps, 'qs) pmapperM = {
      map :
        'a 'g.
        'g G.t -> ('a, 'g, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> ('a, 'qs) Heter.hft M.t;
    }

    val pmapM :
      ('a, ('p, 'ps) cons, 'qs) pmapperM ->
      ('a, nil, ('p, 'ps) cons) Heter.hgt ->
      'qs Tlist.t ->
      ('a, nil, 'qs) Heter.hgt M.t

    type ('asuc, 'ps, 'q) mmapperM = {
      map : 'a 'g. 'g G.t -> ('a, 'g, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> ('a, 'q) F.t M.t;
    }

    val mmapM :
      ('a, ('p, 'ps) cons, 'q) mmapperM ->
      ('a, nil, ('p, 'ps) cons) Heter.hgt ->
      ('a, nil, 'q) gt M.t

    type ('asuc, 'ps) miteratorM = {
      it : 'a 'g. 'g G.t -> ('a, 'g, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> unit M.t;
    }

    val miterM : ('a, ('p, 'ps) cons) miteratorM -> ('a, nil, ('p, 'ps) cons) Heter.hgt -> unit M.t
  end

  module Monadic (M : Monad.Plain) : sig
    module A : module type of Applicative.OfMonad (M)
    include module type of Applicatic (A)
  end

  module IdM : module type of Monadic (Monad.Identity)

  val pmap :
    ('a, ('p, 'ps) cons, 'qs) IdM.pmapperM ->
    ('a, nil, ('p, 'ps) cons) Heter.hgt ->
    'qs Tlist.t ->
    ('a, nil, 'qs) Heter.hgt

  val mmap :
    ('a, ('p, 'ps) cons, 'q) IdM.mmapperM -> ('a, nil, ('p, 'ps) cons) Heter.hgt -> ('a, nil, 'q) gt

  val miter : ('a, ('p, 'ps) cons) IdM.miteratorM -> ('a, nil, ('p, 'ps) cons) Heter.hgt -> unit
end
