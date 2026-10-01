(** Crane bug: inside an instance [TFunctor bundle], the inner [tfmap] over a
    [list operand] field is instantiated at the *enclosing* instance's
    carrier.

    Observed (e0242d8ea), in [TFunctor_bundle]:
      return bundle<std::any>{b.tag,
          tfmap<bundle<std::any>, std::any, std::any>(
              []() { return [](..., List<operand<std::any>> _x1) -> List<operand<std::any>> {...}; }(),
              std::move(f), b.ops)};
    The carrier of this [tfmap] is [fun T => list (operand T)]
    ([TFunctor_list'] at [F := operand]), i.e. [List<operand<std::any>>],
    not [bundle<std::any>].  Diagnostic:
      error: no matching function for call to 'tfmap'
      note: no known conversion from 'const List<operand<std::any>>' to
            'bundle<std::any>' for 3rd argument

    Reduced from Vellvm, [Syntax/Traversal.v:655] [TFunctor_operand_bundle]
    ([mk_operand_bundle (ob_tag ob) (tfmap f (ob_ops ob))]); in Vellvm the
    same call is [tfmap<operand_bundle<std::any>, std::any, std::any>], and
    the inner lambda's list type is spelled [List::list<Operand<std::any><std::any>>],
    which is also where Vellvm's 85 parse errors on e0242d8ea start
    ([vellvm_bench.cpp:8018]).  48 [tfmap] errors in Vellvm. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Module TfunctorRecordListField.
  Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

  #[global] Instance TFunctor_list : TFunctor list | 50 := List.map.
  #[global] Instance TFunctor_list' {F} `{TFunctor F}
    : TFunctor (fun T => list (F T)) | 49 :=
    fun U V f => List.map (tfmap f).

  (* Vellvm's LLVMAst: a section over [T : Set], an operand type and a
     record with a [list operand] field. *)
  Section Syntax.
    Variable T : Set.
    Variant operand : Set := Op (t : T).
    Record bundle : Set := mk_bundle { tag : nat ; ops : list operand }.
  End Syntax.
  Arguments Op {T}.
  Arguments mk_bundle {T}.
  Arguments tag {T}.
  Arguments ops {T}.

  #[global] Instance TFunctor_operand : TFunctor operand :=
    fun U V f o => match o with Op t => Op (f t) end.

  (* Traversal.v:655 [TFunctor_operand_bundle] *)
  #[global] Instance TFunctor_bundle : TFunctor bundle :=
    fun U V f b => mk_bundle (tag b) (tfmap f (ops b)).

  Definition b0 : bundle nat := mk_bundle 7 [Op 1; Op 2].
  Definition b1 : bundle nat := tfmap S b0.
  Definition total : nat := fold_left (fun acc o => match o with Op n => acc + n end) (ops b1) 0.
  Definition is_five : bool := Nat.eqb total 5.
End TfunctorRecordListField.

Crane Extraction "tfunctor_record_list_field" TfunctorRecordListField.
