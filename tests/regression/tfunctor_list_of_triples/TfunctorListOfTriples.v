(** Crane bug (runtime): [tfmap] at the plain [list] instance over a list
    of triples, with a pattern lambda that tfmaps two components (one of
    them a [list metadata] through [TFunctor_list']), treats the tuple
    components as boxed.

    Observed (post-2cfc2c7f3 as installed at the time):
      tfmap<List<std::pair<std::pair<Nat, phi<std::any>>, List<metadata<std::any>>>>, ...>(
          [](auto &&_ec0, List<std::any> _ec1) { return TFunctor_list(_ec0, _ec1); },   // list of pairs as list<any>
          [=](const std::pair<...> &pat) { ... std::any_cast<...>(id0) ...             // cast of a typed component
              std::any(tfmap<phi<std::any>, ...>(...)) ...                              // boxed inside the pair
    It compiles; at run time:
      libc++abi: terminating due to uncaught exception of type
      std::bad_any_cast: bad any cast
    With pairs [(id, phi)] and no metadata list the same instance runs
    correctly.

    Reduced from Vellvm, [Syntax/Traversal.v:724] [TFunctor_block]
    ([tfmap (fun '(id,phi,md) => (endo id, tfmap f phi, tfmap f md)) (blk_phis b)]):
    the Vellvm binary's next runtime throw after let_bound_monad_family and
    tfunctor_alias_of_applied, in [Traversal::TFunctor_block] via
    [crane_erase_fn_impl<std::any, std::pair<std::pair<Raw_id, Phi<std::any>>, ...>>]. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Module TfunctorListOfTriples.
  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.
  #[global] Instance TFunctor_list : TFunctor list | 50 := List.map.
  #[global] Instance TFunctor_list' {F} `{TFunctor F} : TFunctor (fun T => list (F T)) | 49 :=
    fun U V f => List.map (tfmap f).

  Section Syntax.
    Variable T : Set.
    Inductive phi : Set := Phi (t : T).
    Inductive metadata : Set := Md (t : T).
    (* Vellvm's LLVMAst block: [blk_phis : list (local_id * phi * list metadata)] *)
    Record block : Set := mk_block { blk_phis : list (nat * phi * list metadata) }.
  End Syntax.
  Arguments Phi {T}. Arguments Md {T}. Arguments mk_block {T}. Arguments blk_phis {T}.

  #[global] Instance TFunctor_phi : TFunctor phi := fun U V f p => match p with Phi t => Phi (f t) end.
  #[global] Instance TFunctor_md : TFunctor metadata := fun U V f p => match p with Md t => Md (f t) end.

  (* Traversal.v:724 [TFunctor_block]: tfmap at plain [list] (TFunctor_list)
     over pairs, with a pattern lambda that tfmaps a component. *)
  #[global] Instance TFunctor_block : TFunctor block :=
    fun U V f b => mk_block (tfmap (fun '(id, p, md) => (id, tfmap f p, tfmap f md)) (blk_phis b)).

  Definition b0 : block nat := mk_block [(1, Phi 2, [Md 5])].
  Definition b1 : block nat := tfmap S b0.
  Definition total : nat := match blk_phis b1 with (id, Phi t, _) :: _ => id + t | [] => 0 end.
  Definition is_four : bool := Nat.eqb total 4.
End TfunctorListOfTriples.

Crane Extraction "tfunctor_list_of_triples" TfunctorListOfTriples.
