(** A generic lambda reaches [crane_erase_fn]'s callability probe, and the
    probe instantiates it at [std::any], where its structured binding tries to
    decompose [std::any] itself.

    Vellvm's [TFunctor_modul] (rocq/Syntax/Traversal.v:859) maps over its type
    definitions with a pattern lambda:

        tfmap (fun '(id,t) => (id, f t)) (m_type_defs m)

    Crane emits the pattern as a structured binding inside a *generic* lambda,
    and [Traversal::tfmap] passes it to [crane_erase_fn]:

        [=](const auto& pat) mutable {
          const auto& [id, t] = pat;
          return std::make_pair(std::any(std::any_cast<Ident>(id)),
                                std::any(crane_call_erased(f, t)));
        }

    In [crane_erase_fn] (theories/cpp/crane_fn.h:94) the first branch,
    [requires { std::function{f}; }], cannot fire -- CTAD does not apply to a
    generic lambda -- so control reaches the second:

        } else if constexpr (!requires { f(std::declval<std::any>()); }) {

    which substitutes [std::any] for [pat].  The structured binding is in the
    lambda's *body*, not its signature, so this is not a substitution failure
    that the probe can absorb.  It is a hard error, twice, one per private
    member:

        error: cannot bind private member '__h_' of 'std::any'
        error: cannot bind private member '__s_' of 'std::any'

    The instantiation chain in Vellvm, shortest first:

        Traversal::tfmap<List::list, std::pair<Ident, std::any>, LAMBDA,
                         std::pair<std::any, std::any>>       vellvm_bench.h:13003
          -> crane_erase_fn<std::any, LAMBDA&>                vellvm_bench.h:12791
            -> requires { f(std::declval<std::any>()) }       crane_fn.h:95

    This surfaced at 486862356 only because the carrier fix let instantiation
    reach it; the lambda itself is unchanged.

    NOTE ON MEASURING IT: compile the .cpp, not the .h.  [run] is only declared
    in the header, so nothing instantiates the template and the header alone
    reports zero errors.

    Expected: the probe is well-formed and selects a branch, rather than being
    a hard error.
*)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.
#[global] Instance TFunctor_list : TFunctor list | 50 := List.map.

Record ident : Set := mk_ident { i_name : nat }.

Record box (T : Set) : Set := mk_box { b_payload : T }.
#[global] Instance TFunctor_box : TFunctor box | 50 :=
  fun U V f b => mk_box _ (f (b_payload _ b)).

Record pairs (T : Set) (Body : Set) : Set :=
  mk_pairs { p_defs : list (ident * T) ; p_body : Body }.

(* generic in [FnBody], so the element type is erased at the call *)
#[global] Instance TFunctor_pairs {FnBody : Set -> Set} `{TFunctor FnBody}
  : TFunctor (fun T => pairs T (FnBody T)) | 50 :=
  fun U V f m => mk_pairs _ _ (tfmap (fun '(id, t) => (id, f t)) (p_defs _ _ m))
                              (tfmap f (p_body _ _ m)).

Definition run (m : pairs nat (box nat)) : pairs bool (box bool) :=
  tfmap (Nat.ltb 3) m.

Crane Extraction "erased_pair_pattern_probed_at_any" run.
