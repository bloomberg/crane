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

(** [e] converted to the integer type [t], asserting [t] holds its value. *)
Definition exact (t : IntType) (e : Term) : Term := Convert Exact (Int t) e.

(** [e] converted to the integer type [t] as C++ converts integers:
    modulo two to the width of [t]. *)
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

(** The standard library: [<algorithm>], [std::min], [std::max]. *)
Definition std_flavour : Flavour :=
  {| flavour_algorithm := "algorithm"%pstring; flavour_min := "std::min"%pstring;
     flavour_max := "std::max"%pstring |}.

(** BDE: [bsl_algorithm.h], [bsl::min], [bsl::max]. *)
Definition bde_flavour : Flavour :=
  {| flavour_algorithm := "bsl_algorithm.h"%pstring; flavour_min := "bsl::min"%pstring;
     flavour_max := "bsl::max"%pstring |}.

(** The contract arguments [args], each used as [use]. *)
Definition uses (use : InputUse) (args : list string) : list ArgumentSpec :=
  map (fun x => {| argument_name := x; argument_use := use |}) args.

(** An operation with an effect, reading each argument named in [args], in
    order, and returning a value computed by [body]. *)
Definition effect {d : Declaration} (headers : list string) (args : list string) (body : Term)
  : OperationMapping d :=
  {| operation_headers := headers;
     operation_cpp := Structured body;
     operation_contract := EffectfulOperation (uses Read args) ReturnValue [] |}.

(** An operation with an effect, reading each argument named in [args] in
    its canonical representation (text may use any member of it), whose
    C++ is any construction: [Expr] or [WithBody] text is for what [Term]
    cannot say (statements, loops, lambdas). *)
Definition effect_cpp {d : Declaration} (headers : list string) (args : list string)
  (cpp : Construction) : OperationMapping d :=
  {| operation_headers := headers;
     operation_cpp := cpp;
     operation_contract := EffectfulOperation (uses ReadCanonical args) ReturnValue [] |}.

(** A pure operation building a value from the arguments named in [args],
    each taken (moved in at its last use), whose C++ is any construction. *)
Definition builds {d : Declaration} (headers : list string) (args : list string) (cpp : Construction)
  : OperationMapping d :=
  {| operation_headers := headers;
     operation_cpp := cpp;
     operation_contract := PureOperation (uses Take args) ReturnValue [] |}.

(** The identity on the argument [x], the arguments [before] and [after] it
    ignored: an injection or coercion that has no C++ of its own. *)
Definition pass_through {d : Declaration} (before : list string) (x : string) (after : list string)
  : OperationMapping d :=
  {| operation_headers := [];
     operation_cpp := Structured (Arg x);
     operation_contract :=
       PureOperation (uses Ignore before ++ uses ReadCanonical [x] ++ uses Ignore after) ReturnValue [] |}.

(** A dictionary, which is a C++ type: text naming the operation's type
    arguments [%tN].  A class whose one method is its definition has the
    method's arguments, [args], which the dictionary ignores. *)
Definition dictionary {d : Declaration} (headers : list string) (args : list string) (cpp : string)
  : OperationMapping d :=
  {| operation_headers := headers;
     operation_cpp := Expr cpp;
     operation_contract := PureOperation (uses Ignore args) ReturnValue [] |}.

(** A pure operation reading each argument named in [args] in its canonical
    representation, whose C++ is any construction. *)
Definition pure_cpp {d : Declaration} (headers : list string) (args : list string) (cpp : Construction)
  : OperationMapping d :=
  {| operation_headers := headers;
     operation_cpp := cpp;
     operation_contract := PureOperation (uses ReadCanonical args) ReturnValue [] |}.

(** An operation with an effect, its arguments used as [args] says, whose
    C++ is any construction. *)
Definition effect_args {d : Declaration} (headers : list string) (args : list ArgumentSpec)
  (cpp : Construction) : OperationMapping d :=
  {| operation_headers := headers;
     operation_cpp := cpp;
     operation_contract := EffectfulOperation args ReturnValue [] |}.

(** An abstract type mapped to [cpp]: read by value and copied bit by bit
    where [copy] is [BitCopy], else read by [const] reference. *)
Definition value_type {T : Type} (headers : list string) (cpp : TypeExpr) (copy : CopyModel)
  : TypeMapping T :=
  {| type_headers := headers;
     type_cpp := cpp;
     type_components := [];
     type_copy := copy;
     type_access :=
       ReadOnlyValue (match copy with BitCopy => ReadByValue | _ => ReadByConstReference end);
     type_views := NoViews T;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** The constructor [d] of an event family, performed by the C++ [cpp],
    [%aN] its field [N]. *)
Definition event (d : Declaration) (cpp : string) : ConstructorMapping :=
  {| ctor_source := d; ctor_build := Expr cpp; ctor_view := None |}.

(** An event family: it has no C++ type, an event being performed where it
    is triggered, so each constructor is the C++ that performs it
    ([event]). *)
Definition event_family {E : Type} (headers : list string) (ctors : list ConstructorMapping)
  : TypeMapping E :=
  {| type_headers := headers;
     type_cpp := Name "";
     type_components := [];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews E;
     type_interface := AlgebraicInterface ctors;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
