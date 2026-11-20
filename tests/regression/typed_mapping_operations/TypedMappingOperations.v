(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Operation mappings ([OperationMapping (Ref op)], design 11):

    - [Counter], an abstract type mapped to [std::int64_t], used only
      through operation mappings: pure [Read] operations, one that splices
      its argument twice ([counter_double]), and an effectful one
      ([counter_log]).
    - [combine] splices its second argument twice and its first after it;
      [ignore_first] ignores its first argument.  Called on [tick]s (a
      legacy inline constant with an effect), each argument is evaluated
      once, in source order, before the template (design 11.9).
    - [Buffer], mapped to a copy-counting C++ type passed by [const&]:
      [buffer_push] takes its buffer ([Take]), so a function passing its
      parameter there owns it, moves it at its last use and copies it where
      it is still live; [buffer_size] only reads it ([Read]).
    - [Cell], a mutable handle written in place ([Write]): borrowed.
    - [Box A], a parametric type: [%stored(element)] in an operation
      template names the C++ type of the element, found in the type of an
      argument or of the result, and the erased type parameter takes no
      argument.

    The diagnostics: an argument list that does not match the retained
    runtime binders, [Write] on a read-only type, and an operation mapped
    both by a legacy command and by an instance. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Open Scope pstring_scope.

Definition support : string := "typed_mapping_operations_support.h".

Axiom Counter : Type.
Axiom counter_start : nat -> Counter.
Axiom counter_add : Counter -> nat -> Counter.
Axiom counter_value : Counter -> nat.
Axiom counter_double : Counter -> Counter.
Axiom counter_log : Counter -> Counter.

Axiom tick : nat -> nat.
Crane Extract Inlined Constant tick => "ops_support::tick(%a0)"
  From "typed_mapping_operations_support.h".

Axiom combine : nat -> nat -> nat.
Axiom ignore_first : nat -> nat -> nat.

Axiom Buffer : Type.
Axiom buffer_empty : Buffer.
Axiom buffer_push : Buffer -> nat -> Buffer.
Axiom buffer_size : Buffer -> nat.
Axiom checked_push : forall (n : nat) (H : n <> 0) (b : Buffer), Buffer.

Axiom Cell : Type.
Axiom cell_new : nat -> Cell.
Axiom cell_poke : Cell -> nat -> Cell.
Axiom cell_read : Cell -> nat.

Axiom Box : Type -> Type.
Axiom box_fill : forall {A : Type}, nat -> A -> Box A.
Axiom box_at : forall {A : Type} (b : Box A) (i : nat), A.
Axiom box_push : forall {A : Type} (b : Box A) (x : A), Box A.

#[export] Instance counter_mapping : TypeMapping Counter :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Name "std::int64_t";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Counter;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance counter_start_mapping : OperationMapping (Ref counter_start) :=
  {| operation_headers := ["cstdint"];
     operation_cpp := Expr "static_cast<std::int64_t>(%arg(n))";
     operation_contract :=
       PureOperation [{| argument_name := "n"; argument_use := Read |}] ReturnValue [] |}.

#[export] Instance counter_add_mapping : OperationMapping (Ref counter_add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(c) + static_cast<std::int64_t>(%arg(n)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "c"; argument_use := Read |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance counter_value_mapping : OperationMapping (Ref counter_value) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<std::uint64_t>(%arg(c))";
     operation_contract :=
       PureOperation [{| argument_name := "c"; argument_use := Read |}] ReturnValue [] |}.

#[export] Instance counter_double_mapping : OperationMapping (Ref counter_double) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(c) + %arg(c))";
     operation_contract :=
       PureOperation [{| argument_name := "c"; argument_use := Read |}] ReturnValue [] |}.

#[export] Instance counter_log_mapping : OperationMapping (Ref counter_log) :=
  {| operation_headers := [support];
     operation_cpp := Expr "ops_support::log_counter(%arg(c))";
     operation_contract :=
       EffectfulOperation [{| argument_name := "c"; argument_use := Read |}] ReturnValue
         [ExternalEffect "trace"] |}.

#[export] Instance combine_mapping : OperationMapping (Ref combine) :=
  {| operation_headers := [support];
     operation_cpp := Expr "ops_support::combine(%arg(b), %arg(a), %arg(a))";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance ignore_first_mapping : OperationMapping (Ref ignore_first) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(b) + 1)";
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Ignore |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance buffer_mapping : TypeMapping Buffer :=
  {| type_headers := [support];
     type_cpp := Crane.Cpp.Name "ops_support::buffer";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews Buffer;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance buffer_empty_mapping : OperationMapping (Ref buffer_empty) :=
  {| operation_headers := [support];
     operation_cpp := Expr "ops_support::buffer{}";
     operation_contract := PureOperation [] ReturnValue [] |}.

#[export] Instance buffer_push_mapping : OperationMapping (Ref buffer_push) :=
  {| operation_headers := [support];
     operation_cpp := Expr "ops_support::push(%arg(b), %arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "b"; argument_use := Take |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance buffer_size_mapping : OperationMapping (Ref buffer_size) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<std::uint64_t>(%arg(b).items.size())";
     operation_contract :=
       PureOperation [{| argument_name := "b"; argument_use := Read |}] ReturnValue [] |}.

(** The proof [H] is erased: the arguments are [n] and [b]. *)
#[export] Instance checked_push_mapping : OperationMapping (Ref checked_push) :=
  {| operation_headers := [support];
     operation_cpp := Expr "ops_support::push(%arg(b), %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Take |}]
         ReturnValue [] |}.

#[export] Instance cell_mapping : TypeMapping Cell :=
  {| type_headers := ["memory"; "cstdint"];
     type_cpp := Crane.Cpp.Apply "std::shared_ptr" [Crane.Cpp.TypeArg (Crane.Cpp.Name "std::int64_t")];
     type_components := [];
     type_copy := RetainIdentity;
     type_access := MutableHandle HandleByConstReference;
     type_views := NoViews Cell;
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance cell_new_mapping : OperationMapping (Ref cell_new) :=
  {| operation_headers := ["memory"];
     operation_cpp := Expr "std::make_shared<std::int64_t>(static_cast<std::int64_t>(%arg(n)))";
     operation_contract :=
       EffectfulOperation [{| argument_name := "n"; argument_use := Read |}]
         (ReturnFreshIdentity []) [] |}.

#[export] Instance cell_poke_mapping : OperationMapping (Ref cell_poke) :=
  {| operation_headers := [support];
     operation_cpp := Expr "ops_support::poke(%arg(c), %arg(n))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "c"; argument_use := Write |};
          {| argument_name := "n"; argument_use := Read |}]
         (ReturnSameIdentity "c") [] |}.

#[export] Instance cell_read_mapping : OperationMapping (Ref cell_read) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<std::uint64_t>(*%arg(c))";
     operation_contract :=
       PureOperation [{| argument_name := "c"; argument_use := Read |}] ReturnValue [] |}.

#[export] Instance box_mapping (A : Type) : TypeMapping (Box A) :=
  {| type_headers := ["vector"];
     type_cpp :=
       Crane.Cpp.Apply "std::vector" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components := [{| component_name := "element"; component_type := KnownType A |}];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (Box A);
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance box_fill_mapping (A : Type) : OperationMapping (Ref (@box_fill A)) :=
  {| operation_headers := ["vector"; "cstddef"];
     operation_cpp := Expr "std::vector<%stored(element)>(static_cast<std::size_t>(%arg(n)), %arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance box_at_mapping (A : Type) : OperationMapping (Ref (@box_at A)) :=
  {| operation_headers := [];
     operation_cpp := Expr "%stored(element)(%arg(b)[%arg(i)])";
     operation_contract :=
       PureOperation
         [{| argument_name := "b"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance box_push_mapping (A : Type) : OperationMapping (Ref (@box_push A)) :=
  {| operation_headers := ["vector"];
     operation_cpp :=
       WithBody "%arg(b)" "%result.push_back(%stored(element)(%arg(x)));";
     operation_contract :=
       PureOperation
         [{| argument_name := "b"; argument_use := Take |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

Module TypedMappingOperations.

Definition counted (n : nat) : nat :=
  counter_value (counter_add (counter_start n) 2).

Definition doubled (c : Counter) : Counter := counter_double (counter_log c).

Definition ordered (x y : nat) : nat := combine (tick x) (tick y).

Definition skipped (x y : nat) : nat := ignore_first (tick x) (tick y).

Definition skipped_pure (x y : nat) : nat := ignore_first x (tick y).

Definition size_of (b : Buffer) : nat := buffer_size b.

Definition push_one (b : Buffer) : Buffer := buffer_push b 1.

Definition push_keep (b : Buffer) : Buffer * nat :=
  let c := buffer_push b 1 in (c, buffer_size b).

Definition checked_one (b : Buffer) : Buffer := checked_push 1 (fun H => O_S 0 (eq_sym H)) b.

Definition poke_twice (c : Cell) : nat := cell_read (cell_poke (cell_poke c 1) 2).

Definition fresh_cell (n : nat) : nat := cell_read (cell_new n).

Definition boxed (n : nat) (b : bool) : bool := box_at (box_fill n b) 0.

Definition box_third {A : Type} (b : Box A) : A := box_at b 2.

Definition box_push_one {A : Type} (b : Box A) (x : A) : Box A := box_push b x.

End TypedMappingOperations.

Crane Extraction "typed_mapping_operations" TypedMappingOperations.

(** The contract's arguments are the retained runtime binders, in source
    order: [two_args] has two (its type parameter is erased). *)
Axiom two_args : forall {A : Type}, A -> nat -> A.

Module TooFewArguments.
  #[export] Instance bad (A : Type) : OperationMapping (Ref (@two_args A)) :=
    {| operation_headers := [];
       operation_cpp := Expr "%arg(x)";
       operation_contract :=
         PureOperation [{| argument_name := "x"; argument_use := Read |}] ReturnValue [] |}.
  Crane Check Mapping (@two_args nat) Fails With
    "the contract declares 1 argument (x), but the operation has 2 retained runtime binders (_, _)".
End TooFewArguments.

Axiom named_args : forall {A : Type} (x : A) (n : nat), A.

Module WrongOrder.
  #[export] Instance bad (A : Type) : OperationMapping (Ref (@named_args A)) :=
    {| operation_headers := [];
       operation_cpp := Expr "%arg(x)";
       operation_contract :=
         PureOperation
           [{| argument_name := "n"; argument_use := Read |};
            {| argument_name := "x"; argument_use := Read |}]
           ReturnValue [] |}.
  Crane Check Mapping (@named_args nat) Fails With
    "argument ""n"" is bound to the runtime binder ""x""".
End WrongOrder.

Module RightOrder.
  #[export] Instance good (A : Type) : OperationMapping (Ref (@named_args A)) :=
    {| operation_headers := [];
       operation_cpp := Expr "%arg(x)";
       operation_contract :=
         PureOperation
           [{| argument_name := "x"; argument_use := Read |};
            {| argument_name := "n"; argument_use := Ignore |}]
           ReturnValue [] |}.
  Crane Check Mapping (@named_args nat) Selects good.
End RightOrder.

(** [Write] needs a mutable type: [Counter] is a read-only value. *)
Axiom counter_bump : Counter -> Counter.

Module WriteReadOnly.
  #[export] Instance bad : OperationMapping (Ref counter_bump) :=
    {| operation_headers := [];
       operation_cpp := Expr "++%arg(c)";
       operation_contract :=
         EffectfulOperation [{| argument_name := "c"; argument_use := Write |}] ReturnValue [] |}.
  Crane Check Mapping counter_bump Fails With
    "argument ""c"" is written, but its type's access model is read-only".
End WriteReadOnly.

(** An operation mapped both by a legacy command and by an instance. *)
Axiom dual_op : nat -> nat.
Crane Extract Inlined Constant dual_op => "(%a0 + 1)".

Module DualMapping.
  #[export] Instance dual_op_mapping : OperationMapping (Ref dual_op) :=
    {| operation_headers := [];
       operation_cpp := Expr "(%arg(n) + 2)";
       operation_contract :=
         PureOperation [{| argument_name := "n"; argument_use := Read |}] ReturnValue [] |}.
End DualMapping.

Module UsesDual.
Definition dual_three : nat := dual_op 3.
End UsesDual.

Import DualMapping.
Fail Crane Extraction "typed_mapping_operations_dual" UsesDual.
