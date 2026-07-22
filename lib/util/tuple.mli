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

  type ('asuc, 'g0, 'ps, 'qs) pmapper = {
    map : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> ('a, 'qs) Heter.hft;
  }

  val pmap :
    ('a, 'g0, ('p, 'ps) cons, 'qs) pmapper ->
    ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt ->
    'qs Tlist.t ->
    ('a, nil, 'g0, 'qs) Heter.hgt

  type ('asuc, 'g0, 'ps, 'q) mmapper = {
    map : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> ('a, 'q) F.t;
  }

  val mmap :
    ('a, 'g0, ('p, 'ps) cons, 'q) mmapper ->
    ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt ->
    ('a, nil, 'g0, 'q) gt

  type ('asuc, 'g0, 'ps) miterator = {
    it : 'a. ('a, 'g0, 'asuc) Tbwd.insert -> ('a, 'ps) Heter.hft -> unit;
  }

  val miter :
    ('a, 'g0, ('p, 'ps) cons) miterator -> ('a, nil, 'g0, ('p, 'ps) cons) Heter.hgt -> unit
end
