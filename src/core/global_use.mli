(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Global_use]: building and reading the use of a global (the payload
    of [Core.Expr.Global]) -- the callee, what the use instantiates the
    callee's type scheme at, and the use's occurrence. *)

open Names

(** [Monomorphic] for a callee whose scheme has no variable; otherwise
    [Polymorphic] with one instantiation slot per scheme variable. *)
type 'p instance = 'p Grammar.Global_use.instance =
  | Monomorphic
  | Polymorphic of 'p Type.at Scheme.Instantiation.t

(** A global named at a use: read anywhere, built only here. *)
type 'p at = 'p Grammar.Global_use.at = private {
  callee : GlobRef.t;
  instance : 'p instance;
  occurrence : Occurrence.t;
}

(** A use in the frozen program ({!Phase.frozen}). *)
type t = Phase.frozen at

(** A use in the extracted program, which may hold metavariables. *)
type extracted = Phase.extracted at

(** The global used. *)
val callee : 'p at -> GlobRef.t

(** A use of a declaration known to quantify nothing. *)
val monomorphic : GlobRef.t -> 'p at

(** A use at an instantiation; [monomorphic] when the scheme has no
    variable. *)
val polymorphic : GlobRef.t -> 'p Type.at Scheme.Instantiation.t -> 'p at

(** An open occurrence of a polymorphic declaration: every variable a
    fresh hole, nothing written. *)
val infer_all : GlobRef.t -> Scheme.Id.t -> 'p at

(** A declaration's reference to itself within its own body: every
    variable stands for itself. *)
val identity : GlobRef.t -> Scheme.Id.t -> 'p at

(** [None] for a monomorphic use. *)
val instantiation : 'p at -> 'p Type.at Scheme.Instantiation.t option

(** The arguments the source wrote, by the variable each was written for;
    one extraction could not read is [Core.Type.Erased Type_argument], the erased
    argument it stood as. *)
val written_evidence : 'p at -> (Scheme.Var.t * 'p Type.at) list

(** The occurrence telling this use apart from every other. *)
val occurrence : 'p at -> Occurrence.t

(** The use, as a new occurrence: for a copy that is new terms. *)
val refresh : 'p at -> 'p at

(** Maps every type of the instantiation, keeping the scheme, the slots'
    evidence, the holes and the occurrence. *)
val map_types : ('p Type.at -> 'p Type.at) -> 'p at -> 'p at

(** Every type of the instantiation: solutions and written arguments. *)
val iter_types : ('p Type.at -> unit) -> 'p at -> unit

(** Whether some type of the instantiation ({!iter_types}) satisfies the
    predicate. *)
val exists_type : ('p Type.at -> bool) -> 'p at -> bool
