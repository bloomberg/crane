(** Crane bug: a constructor whose continuation field's domain is computed
    from another field ([Mchoose (c : MemC) (k : memCType c -> MemS A)],
    [memCType] a type-level function, erased to [std::any]) is built from a
    generic function taking the continuation at the *concrete* domain.

    Observed (post-pattern_binder_state_boxed install):
      template <typename T1, typename F0> static MemS<T1> Mfresh_prov(F0 &&k) {
        return MemS<T1>::mchoose(MemC::CFRESH_PROV, k);   // k : bool -> MemS<T1>
      }
      static MemS<T1> mchoose(MemC c, std::function<MemS<T1>(memCType)> k);   // memCType = std::any
    Diagnostic:
      error: no viable conversion from '(lambda ...)' to
             'std::function<MemS<bool> (memCType)>' (aka 'std::function<MemS<bool> (std::any)>')
    The continuation needs adapting at the erased domain (take [std::any],
    [any_cast] to the concrete type the choice fixes) when it is stored.

    Reduced from Vellvm's memory model ([MemS] / [Mchoose] / [memCType] in
    [Semantics/Interfaces/Memory.v]; [Memory0::Mfresh_prov] and
    [Memory0::Mnext_key]): 2 of Vellvm's 8 remaining errors, plus the
    crane_fn.h functional cast. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module DependentChoiceContinuation.
  (* Vellvm's MemoryModel MemS: a free monad whose choice node's
     continuation takes a value of a type computed from the choice. *)
  Inductive MemC : Type := cnext_key | cfresh_prov.
  Definition memCType (c : MemC) : Type := match c with cnext_key => nat | cfresh_prov => bool end.

  Inductive MemS (A : Type) : Type :=
  | MRet (a : A)
  | Mchoose (c : MemC) (k : memCType c -> MemS A).
  Arguments MRet {A}. Arguments Mchoose {A}.

  (* [Mfresh_prov k := Mchoose cfresh_prov k] *)
  Definition Mfresh_prov {A} (k : bool -> MemS A) : MemS A := Mchoose cfresh_prov k.
  Definition fresh_prov : MemS bool := Mfresh_prov (fun p => MRet p).

  Definition run (m : MemS bool) : bool :=
    match m with
    | MRet a => a
    | Mchoose c k => match c as c0 return (memCType c0 -> MemS bool) -> bool with
                     | cfresh_prov => fun k => match k true with MRet b => b | _ => false end
                     | cnext_key => fun _ => false
                     end k
    end.
  Definition is_true : bool := run fresh_prov.
End DependentChoiceContinuation.

Crane Extraction "dependent_choice_continuation" DependentChoiceContinuation.
