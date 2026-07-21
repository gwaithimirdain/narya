open Signatures
open Tlist
open Tbwd

module Make (G : Decidable) (F : Fam2) : sig
  module W : module type of Word.Make (G)

  type ('a, 'b, 'g0, 'p) gt
  type ('a, 'g0, 'p) t = ('a, nil, 'g0, 'p) gt

  val empty : (W.zero, 'g0, 'p) t
  val find : ('a, 'g0, 'asuc) Tbwd.insert -> ('asuc, 'g0, 'p) t -> ('a, 'p) F.t
  val set : ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'p) F.t -> ('asuc, 'g0, 'p) t -> ('asuc, 'g0, 'p) t

  val update :
    ('a, 'g0, 'asuc) Tbwd.insert ->
    (('a, 'p) F.t -> ('a, 'p) F.t) ->
    ('asuc, 'g0, 'p) t ->
    ('asuc, 'g0, 'p) t

  type ('asuc, 'g0, 'p) builder = { build : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'p) F.t }

  val build : 'a W.t -> 'g0 G.t -> ('a, 'g0, 'p) builder -> ('a, 'g0, 'p) t

  module Heter : sig
    type (_, _) hft =
      | [] : ('a, nil) hft
      | ( :: ) : ('a, 'p) F.t * ('a, 'ps) hft -> ('a, ('p, 'ps) cons) hft

    type (_, _, _, _) hgt =
      | [] : ('a, 'b, 'g0, nil) hgt
      | ( :: ) :
          ('a, 'b, 'g0, 'p) gt * ('a, 'b, 'g0, 'ps) hgt
          -> ('a, 'b, 'g0, ('p, 'ps) cons) hgt
  end

  module Applicatic (M : Applicative.Plain) : sig
    type ('asuc, 'g0, 'ps, 'qs) pmapperM = {
      map : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> ('a, 'qs) Heter.hft M.t;
    }

    val pmapM :
      ('a, 'g0, ('p, 'ps) cons, 'qs) pmapperM ->
      ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt ->
      'qs Tlist.t ->
      ('a, nil, 'g0, 'qs) Heter.hgt M.t

    type ('asuc, 'g0, 'ps, 'q) mmapperM = {
      map : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> ('a, 'q) F.t M.t;
    }

    val mmapM :
      ('a, 'g0, ('p, 'ps) cons, 'q) mmapperM ->
      ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt ->
      ('a, nil, 'g0, 'q) gt M.t

    type ('asuc, 'g0, 'ps) miteratorM = {
      it : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> unit M.t;
    }

    val miterM :
      ('a, 'g0, ('p, 'ps) cons) miteratorM -> ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt -> unit M.t
  end

  module Monadic (M : Monad.Plain) : sig
    module A : module type of Applicative.OfMonad (M)
    include module type of Applicatic (A)
  end

  module IdM : module type of Monadic (Monad.Identity)

  val pmap :
    ('a, 'g0, ('p, 'ps) cons, 'qs) IdM.pmapperM ->
    ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt ->
    'qs Tlist.t ->
    ('a, nil, 'g0, 'qs) Heter.hgt

  val mmap :
    ('a, 'g0, ('p, 'ps) cons, 'q) IdM.mmapperM ->
    ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt ->
    ('a, nil, 'g0, 'q) gt

  val miter :
    ('a, 'g0, ('p, 'ps) cons) IdM.miteratorM -> ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt -> unit
end
