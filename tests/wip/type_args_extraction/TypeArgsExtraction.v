(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Type arguments to a function can be referred to with %t0,%t1,..., but they are
    extracted as std::any. Accessing those arguments during extraction is invaluable for
    correctly typing output terms, particularly lambda arguments passed to ITree loop combinators. *)

From ITree Require Import
  ITree
  ITreeFacts
.

From Crane Require Import Monads.ITree.   



Definition double_n_body (n : nat) : itree ((callE nat nat) +' void1) nat :=
  match n with
  | O => Ret 0
  | Datatypes.S x =>
      x' <- call x;;
      Ret (2 + x') 
  end.


Definition double_n (n : nat) : itree void1 nat
  := Eval unfold double_n_body in (rec double_n_body n).


Require Import Crane.Mapping.NatIntStd.


(* rec extraction, note that type arguments %t2,%t1 become std::any*)
Crane Extract Inlined Constant rec =>
        "
         [&]() -> %t2 {
         static  std::function<%t1(%t2)> __self;
         __self = %a0;
         return __self(%a1);;
 }()
" From "functional".
Crane Extract Inlined Constant call => "__self(%a0)".


(* NOTE: it extracts and tests correctly with the following specialized custom directive. *)
(* Crane Extract Inlined Constant rec =>
 *         "
 *          [&]() -> uint64_t {
 *          static  std::function<uint64_t(uint64_t)> __self;
 *          __self = %a0;
 *          return __self(%a1);;
 *  }()
 * " From "functional". *)


Crane Extraction "type_args_extraction" double_n.
