From Crane Require Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List Ascii String.
Import ListNotations.

Crane Extract Inductive Ascii.ascii => "char"
  [ "(static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0)))" ]
  "bool %b0a0 = %scrut & 1; bool %b0a1 = (%scrut >> 1) & 1; bool %b0a2 = (%scrut >> 2) & 1; bool %b0a3 = (%scrut >> 3) & 1; bool %b0a4 = (%scrut >> 4) & 1; bool %b0a5 = (%scrut >> 5) & 1; bool %b0a6 = (%scrut >> 6) & 1; bool %b0a7 = (%scrut >> 7) & 1; %br0"
  From "".

Crane Extract Inductive String.string => "std::string"
  [ "std::string()"
    "std::string(1, %a0) + %a1" ]
  "if (%scrut.empty()) { %br0 } else { char %b1a0 = %scrut[0]; std::string %b1a1 = %scrut.substr(1); %br1 }"
  From "string".

Crane Extract Inlined Constant String.append => "%a0 + %a1".
Crane Extract Inlined Constant String.eqb => "(%a0 == %a1)".

(** [sigt_leaf_forward_string] reproduced the case where the destructured
    leaf is forwarded into a *functor/closure parameter* whose concrete type
    is only known at template instantiation, and got fixed via
    [crane_call_erased]. This test is different: the "consumer"
    (`wrap_string : string -> bool`) is a plain TOP-LEVEL Coq function with an
    already fully concrete, statically-known signature at the point the
    literal action closure is *written* (domain `domty 0` is a concrete alias
    for `string * unit`, not behind any module abstraction) -- the erasure
    only shows up later, when a *different* piece of code (`run`) accesses the
    same closure generically through a value-dependent match on a
    runtime-varying index. This matches Parser.v's
    `find_predicate_and_action` / grammar-table shape far more closely than
    the functor version.

    This used to fail to *compile*: because the literal closure is stored via
    [existT] into an erased [std::any] field, [mark_own_param_for_pair_erasure]
    forced the lambda's self-destructure to go through
    [any_cast<pair<any,any>>], on the assumption (true for the functor case)
    that such a lambda's parameter always ends up generic/erased. Here the
    domain `domty 0` resolves to a fully *concrete* type at this literal (a
    literal index `0`, not an abstract parameter), so the lambda's C++
    parameter is rendered with its real concrete type -- and any_cast-ing an
    already-concrete pair as if it were [std::any] does not compile. Fixed by
    only forcing that rewrite when the lambda's own parameter type is
    actually erased/generic at this instantiation. *)
Definition wrap_string (s : string) : bool := String.eqb s s.

Definition domty (n : nat) : Type :=
  match n with
  | 0 => (string * unit)%type
  | _ => (nat * unit)%type
  end.

Definition prod2 : Type := (nat * list nat)%type.
Definition pred_ty (p : prod2) : Type := let (n, _) := p in domty n -> bool.
Definition act_ty (p : prod2) : Type := let (n, _) := p in domty n -> bool.
Definition psem (p : prod2) : Type := (pred_ty p * act_ty p)%type.
Definition entry : Type := { p : prod2 & psem p }.

Definition my_entry : entry :=
  existT psem (0, [])
    ((fun tup : domty 0 => let (v, _x) := tup in wrap_string v),
     (fun tup : domty 0 => let (v, _x) := tup in wrap_string v)).

Definition garg (n : nat) : domty n :=
  match n with
  | 0 => ("hi"%string, tt)
  | _ => (0, tt)
  end.

Definition run (e : entry) : bool :=
  match e with
  | existT _ (n, _) fg =>
      let (f, _g) := fg in
      if f (garg n) then true else false
  end.

Definition check (u : unit) : bool := run my_entry.
Crane Extraction "sigt_leaf_forward_topfn" check my_entry.
