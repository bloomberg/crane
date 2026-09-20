(* An eta-expanded handler lambda, inside a definition parameterised by a
   typeclass, names a type variable the enclosing head never declares.

   Expected: the inner lambda is generic over the event's index, the way the
   same program emits when the typeclass context is removed:

     []<typename _T2>(const LocalE<_T2>& a0) -> decltype(auto) {
       return handle_local_debug<_T2, ...>(a0); }

   Actual: it was emitted monomorphic, wrapped in an IIFE, and its return type
   named T2, which is not a template parameter of anything in scope:

     template <Params _tcI0, typename T1>
     Monads::template stateT<Big, std::shared_ptr, T1> fused_local(LocalE e) {
       return on_ls<LocalE, T1>(handle_local_stack<LocalE, T1>(
           []() {
             return [](LocalE _x0)
                 -> Monads::template stateT<lenv, std::shared_ptr, T2> {
               return handle_local_debug<_tcI0, LocalE>(_x0); };
           }(), e)); }

     error: use of undeclared identifier 'T2'

   The typeclass context decides which of two broken forms comes out. Delete
   `Context {Pa : Params}` from both sections (and the use of `width`) and the
   identical program emits the generic form above instead -- which does not
   compile either: `LocalE` is an enum, so `const LocalE<_T2> &` does not
   parse, and the `std::invoke_result_t` filler for the second argument is
   nonsense. That face is filed as eta_handler_event_as_template. Both faces
   are the same defect: an eta-expanded handler quantifies an index C++ cannot
   deduce, and neither the lambda nor its consumer says so.

   The free name is now gone: eta-expansion binds the index it invents, as a
   template parameter of the lambda it is building. What is left is the half
   that binding exposes. LocalE is an enum -- erasure took the index out of
   the parameter -- so no argument deduces it, and a template parameter
   nothing can supply is worse than the erasure it replaced: the lambda comes
   out returning stateT<lenv, itree_tc, std::any>, which is honest, and which
   handle_local_stack cannot convert back to its declared T2.

   Deducing it is not on: the enum carries nothing. The index has to be
   supplied, by the one place that knows it -- the consumer, whose own return
   type is stateT<lenv, itree_tc, T2> -- as h.template operator()<T2>(e). No
   machinery for that exists yet; the rank-2 path at translation.ml:5630
   drops an undeducible carrier for exactly the same reason, so this shape is
   outside what either path handles.

   The sibling shape does work, and is the one Vellvm is made of: where the
   event type still carries the index (memM<T2> rather than a bare enum), the
   lambda's parameter deduces it, the template parameter survives, and no
   consumer change is needed.

   Reduced from Vellvm's Semantics/InterpretationStack.v:60-90, where
   fused_local, fused_intrinsic, fused_memory and the OOME/UBE cases of the
   fused handler chain produce nine copies of this error. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
From ExtLib Require Import Structures.Monads.
Import ITree.Basics.Basics.Monads.

Variant LocalE : Type -> Type := | LGet : LocalE nat.
Definition lenv := nat.
Definition Big := (nat * nat)%type.

Class Params := { width : nat }.

Section S.
  Context {Pa : Params}.
  Context {E : Type -> Type}.

  Definition handle_local_debug : LocalE ~> stateT lenv (itree E) :=
    fun _ e => match e in LocalE T return stateT lenv (itree E) T with
               | LGet => fun s => Ret (s, s + width)
               end.

  Definition handle_local_stack (h : LocalE ~> stateT lenv (itree E))
    : LocalE ~> stateT lenv (itree E) := fun T e => h T e.

  Definition on_ls {T} (c : stateT lenv (itree E) T) : stateT Big (itree E) T :=
    fun b => ITree.bind (c (fst b)) (fun sa => Ret ((fst sa, snd b), snd sa)).
End S.

Section T.
  Context {Pa : Params}.

  Definition fused_local : LocalE ~> stateT Big (itree LocalE) :=
    fun T e => on_ls (handle_local_stack handle_local_debug T e).

  Definition use (n : nat) : itree LocalE (Big * nat) := fused_local _ LGet (n, n).
End T.

Module HandlerLambdaTargUndeclared.
  Definition go `{Params} (n : nat) := use n.
End HandlerLambdaTargUndeclared.

Crane Extraction "handler_lambda_targ_undeclared" HandlerLambdaTargUndeclared.
