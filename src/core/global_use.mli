(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Building and reading the use of a global ({!Grammar.Global_use}). *)

open Names

type instance = Grammar.Global_use.instance =
  | Monomorphic
  | Polymorphic of Type.t Scheme.Instantiation.t

(** A global named at a use: read anywhere, built only here. *)
type t = Grammar.Global_use.t = private {
  callee : GlobRef.t;
  instance : instance;
  occurrence : Occurrence.t;
}

val callee : t -> GlobRef.t

(** A use of a declaration known to quantify nothing. *)
val monomorphic : GlobRef.t -> t

(** A use at an instantiation; [monomorphic] when the scheme has no
    variable. *)
val polymorphic : GlobRef.t -> Type.t Scheme.Instantiation.t -> t

(** An open occurrence of a polymorphic declaration: every variable a
    fresh hole, nothing written. *)
val infer_all : GlobRef.t -> Scheme.Id.t -> t

(** A declaration's reference to itself within its own body: every
    variable stands for itself. *)
val identity : GlobRef.t -> Scheme.Id.t -> t

(** [None] for a monomorphic use. *)
val instantiation : t -> Type.t Scheme.Instantiation.t option

(** The arguments the source wrote, by the variable each was written for;
    one extraction could not read is [Type.Erased Type_argument], the erased
    argument it stood as. *)
val written_evidence : t -> (Scheme.Var.t * Type.t) list

val occurrence : t -> Occurrence.t

(** The use, as a new occurrence: for a copy that is new terms. *)
val refresh : t -> t

(** Maps every type of the instantiation, keeping the scheme, the slots'
    evidence, the holes and the occurrence. *)
val map_types : (Type.t -> Type.t) -> t -> t

(** Every type of the instantiation: solutions and written arguments. *)
val iter_types : (Type.t -> unit) -> t -> unit

val exists_type : (Type.t -> bool) -> t -> bool
