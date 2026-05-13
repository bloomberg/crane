(* Regression: zero-argument definitions used in separate extraction
   must be emitted as function calls with (), not bare references.
   Previously Crane generated Class::foo (function reference) instead
   of Class::foo() (function call) for nullary static member functions,
   causing compilation errors like:
     cannot initialize a variable of type 'T' with an lvalue of type 'const T &()'
   This affects both cross-module references (I::_1, S::empty) and
   local references (emptyTable, SigmaEnum) in separately extracted code. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module Type Cfg.
  Parameter default_val : nat.
  Parameter default_list : list nat.
End Cfg.

Module Worker (C : Cfg).

  (* Cross-module nullary ref: C.default_val must be C::default_val() *)
  Definition get_default : nat := C.default_val.

  (* Local nullary def used by another def *)
  Definition local_empty : list nat := nil.

  (* Local nullary ref: local_empty must be local_empty() *)
  Definition local_length : nat := length local_empty.

  (* Cross-module nullary ref in a function body *)
  Definition prepend (x : nat) : list nat := x :: C.default_list.

  (* Cross-module nullary ref as function argument *)
  Definition default_head : nat := hd 0 C.default_list.

End Worker.

Crane Separate Extraction Worker.
