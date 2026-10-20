(* Run an extracted [itree vecE R]: force the tree, perform each event on
   [Vec_impl], and feed the answer to the continuation.  This is the cheapest
   interpreter there is -- no [interp], no handler composition -- so it is the
   most favourable footing the OCaml side can have. *)
module Make (M : sig
  type 'x vecE =
    | VMake of int * Obj.t
    | VGet of 'x Vec_impl.t * int
    | VSet of Obj.t Vec_impl.t * int * Obj.t
    | VLen of Obj.t Vec_impl.t
    | VPush of Obj.t Vec_impl.t * Obj.t
    | VShrink of Obj.t Vec_impl.t * int
    | VAbort of int
  type ('e, 'r, 'itree) itreeF =
    | RetF of 'r
    | TauF of 'itree
    | VisF of 'e * (Obj.t -> 'itree)
  type ('e, 'r) itree = ('e, 'r) __itree Lazy.t
  and ('e, 'r) __itree = Go of ('e, 'r, ('e, 'r) itree) itreeF
end) = struct
  open M
  let handle : type x. Obj.t vecE -> Obj.t = function
    | VMake (n, x) -> Obj.repr (Vec_impl.make n x)
    | VGet (v, i) -> Vec_impl.get (Obj.magic v) i
    | VSet (v, i, x) -> Vec_impl.set v i x; Obj.repr ()
    | VLen v -> Obj.repr (Vec_impl.len v)
    | VPush (v, x) -> Vec_impl.push v x; Obj.repr ()
    | VShrink (v, n) -> Vec_impl.shrink v n; Obj.repr ()
    | VAbort site -> Vec_impl.abort site

  let rec run : type r. (Obj.t vecE, r) itree -> r = fun t ->
    match Lazy.force t with
    | Go (RetF r) -> r
    | Go (TauF t) -> run t
    | Go (VisF (e, k)) -> run (k (handle e))
end
