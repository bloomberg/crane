(** A local fixpoint Core generates in place -- a [[&]] lambda, since it is
    only ever called -- was live across a recursive call Loopify turns into a
    frame push, so Loopify saved the lambda in the continuation frame and
    called it when the frame resumed, after the block declaring what it
    captured by reference had ended.  [k] is such a block local:
      auto map_k = [&](const List<List<uint64_t>> &lsts) { ... k ... };
      _stack.emplace_back(CraneCont_Cons{l, k, std::move(map_k)});
    and the resumed frame called [map_k], reading [k] out of a dead stack
    slot (ASan: stack-use-after-scope; plainly, a later turn's [k]).
    A group a frame keeps across a resume ({!Ownership_ir.kept_by_frame})
    now holds copies, [[=]].  Found by the closure-captures validator
    (Move_check): a lambda whose plan captures by reference never escapes. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

Module InplaceFixSavedInFrame.
  Fixpoint insert_shift (x : nat) (l : list nat) : list (list nat) :=
    match l with
    | nil => [[x]]
    | h :: t =>
      let k := Nat.add h x in
      let fix map_k lsts :=
        match lsts with
        | nil => nil
        | lst :: rest => (k :: lst) :: map_k rest
        end
      in
      (k :: x :: l) :: map_k (insert_shift x t)
    end.

  Definition sum_heads (ls : list (list nat)) : nat :=
    fold_left (fun acc l => match l with nil => acc | h :: _ => Nat.add acc h end) ls 0.

  Definition test : nat := sum_heads (insert_shift 1 [10; 20; 30]).
End InplaceFixSavedInFrame.

Set Crane Loopify.
Crane Extraction "inplace_fix_saved_in_frame" InplaceFixSavedInFrame.
