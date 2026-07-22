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

Module Type SEM.
  Parameter idx : Type.
  Parameter sem : idx -> Type.
End SEM.

(** Same erased-pair-of-functions shape as sigt_prod_fn_any_lit_pair, but the
    leaf value pulled out of the nested-pair destructure (`v`) is *forwarded
    directly* into another function that expects a concrete mapped type
    (`std::string`, via `String.eqb`) rather than just being consumed
    opaquely. This mirrors XML.h's `xmlnode(nm, ...)` call, where `nm` is
    pulled out of a nested `std::any_cast<std::pair<std::any,std::any>>>`
    chain but then handed to `xmlnode` (which expects `std::string`) with no
    final `std::any_cast<std::string>`.

    This used to fail to *compile*: `eq` is itself a functor parameter whose
    domain (`S.sem a`) is abstract, so its C++ type is only concrete once the
    generated template is instantiated with the caller-supplied `String.eqb`
    lambda. Crane's `any_cast` insertion for call arguments only fires when
    the callee's parameter type can be resolved to something concrete at
    translation time ([MLmagic] + [expected_ty] threading); here it can't be
    (the domain type resolves to `std::any`/`Tany` generically), so `v` was
    passed to `eq` raw, and `eq`'s concrete (non-generic) instantiation
    rejected `std::any`. Fixed by routing such calls through the
    `crane_call_erased` runtime helper (`crane_fn.h`), which uses
    `std::function` CTAD — same trick as `crane_erase_fn` — to recover `eq`'s
    concrete parameter types at C++ instantiation time and `any_cast` each
    boxed argument accordingly. *)
Module Make (S : SEM).
  Definition dom (a : S.idx) : Type := (S.sem a * unit)%type.
  Definition prod2 : Type := (S.idx * list S.idx)%type.
  Definition pred_ty (p : prod2) : Type := let (a, _) := p in dom a -> bool.
  Definition act_ty (p : prod2) : Type := let (a, _) := p in dom a -> bool.
  Definition psem (p : prod2) : Type := (pred_ty p * act_ty p)%type.
  Definition entry : Type := { p : prod2 & psem p }.

  Definition mk_entry (a : S.idx) (eq : S.sem a -> S.sem a -> bool) : entry :=
    existT psem (a, [])
      ((fun tup : dom a => let (v, _x) := tup in eq v v),
       (fun tup : dom a => let (v, _x) := tup in eq v v)).

  Definition run (e : entry) (arg : forall a, S.sem a) : bool :=
    match e with
    | existT _ (a, _) fg =>
        let (f, _g) := fg in
        if f (arg a, tt) then true else false
    end.
End Make.

Module Inst <: SEM.
  Definition idx : Type := unit.
  Definition sem : idx -> Type := fun _ => string.
End Inst.

Module M := Make Inst.
Definition my_entry : M.entry := M.mk_entry tt String.eqb.
Definition my_arg : forall a : Inst.idx, Inst.sem a := fun _ => "hi"%string.
Definition check (u : unit) : bool := M.run my_entry my_arg.
Crane Extraction "sigt_leaf_forward_string" check my_entry my_arg.
