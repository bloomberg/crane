(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Helpers for writing operation mappings with structured bodies
    ([Crane.Cpp.Term], documented in [Descriptor.v]).  Plain functions: the
    plugin reduces a descriptor before reading it, so an instance defined
    with them reads as the descriptor they compute. *)
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString BinNums.
From Stdlib Require Import List.
From Stdlib Require Export BinIntDef.
Import ListNotations Crane.Cpp.

(** A pure operation reading each argument named in [args], in order,
    returning a value computed by [body]. *)
Definition pure {d : Declaration} (headers : list string) (args : list string) (body : Term)
  : OperationMapping d :=
  {| operation_headers := headers;
     operation_cpp := Structured body;
     operation_contract :=
       PureOperation
         (map (fun x => {| argument_name := x; argument_use := Read |}) args)
         ReturnValue [] |}.

(** [e] as a [std::size_t], which holds its value. *)
Definition to_size (e : Term) : Term := Convert Exact (Int Size) e.

(** A literal of type [int]: the operand C++ converts to the other side's
    type, as an unsuffixed literal in C++ text is. *)
Definition lit (v : Z) : Term := IntLit I32 v.

(** [e] converted to the integer type [t]: [exact] asserts it holds the
    value, [wrap] reduces it modulo two to the width of [t]. *)
Definition exact (t : IntType) (e : Term) : Term := Convert Exact (Int t) e.
Definition wrap (t : IntType) (e : Term) : Term := Convert Wrap (Int t) e.

(** [Nat.compare]'s and its kin's three-way result, by two comparisons. *)
Definition three_way (x y : Term) : Term :=
  Cond (Binop Less x y) (EnumValue ResultType "LT")
    (Cond (Binop Less y x) (EnumValue ResultType "GT") (EnumValue ResultType "EQ")).

(** What the std and BDE flavours of a mapping spell differently: the
    header and names of [min] and [max]. *)
Record Flavour : Type := {
  flavour_algorithm : string;
  flavour_min : string;
  flavour_max : string
}.

Definition std_flavour : Flavour :=
  {| flavour_algorithm := "algorithm"%pstring; flavour_min := "std::min"%pstring;
     flavour_max := "std::max"%pstring |}.

Definition bde_flavour : Flavour :=
  {| flavour_algorithm := "bsl_algorithm.h"%pstring; flavour_min := "bsl::min"%pstring;
     flavour_max := "bsl::max"%pstring |}.
