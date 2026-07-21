
From Crane Require Import Monads.STMonad.   

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Peano_dec
  Basics
  Classes.EquivDec
  Extraction
  Init.Peano
  Lia
  List
  Morphisms
  PrimString
  RelationClasses
  Relation_Definitions
  Setoid
  Strings.String
.

From ExtLib Require Import
  CmpDec
  Data.Bool
  Data.List
  Data.Map.FMapAList
  Data.Monads.EitherMonad
  Data.Pair
  Data.String
  Structures.Functor
  Structures.Maps
  Structures.Traversable
  Structures.Reducible
.


Import ListNotations.
From Equations Require Import Equations.

Module QuicksortFun. 

  Lemma filter_length {A} (f : A -> bool) (l : list A) :
    length (List.filter f l) <= length l.
  Proof. induction l; simpl; [lia | destruct (f a); simpl; lia]. Qed.

  Equations? quicksort_fun (l : list nat) : list nat by wf (length l) lt :=
    quicksort_fun [] => [];
    quicksort_fun (p :: xs) =>
      quicksort_fun (List.filter (fun x => Nat.ltb x p) xs)
        ++ [p] ++
      quicksort_fun (List.filter (fun x => Nat.leb p x) xs).
  - specialize (filter_length (fun x => Nat.ltb x p) xs) as H. lia.   
  - specialize (filter_length (fun x => Nat.leb p x) xs) as H. lia.   
  Defined.

  
  (* Need to reimport to put in scope for test code. *)
  Definition nth := Eval unfold List.nth in (@List.nth nat).
  Definition len := Eval unfold List.length in (@List.length nat).

  (* NOTE: axiomatized for purposes of applying the intuitive std::to_string here instead of
     printing long strings of (S (S ( S.... )))
   *)
  Axiom int_to_string: forall (n : nat), PrimString.string.

  Fixpoint list_to_string_helper (l : list nat) : PrimString.string :=
    match l with
    | nil => ""
    | x::xs => PrimString.cat (int_to_string x) (PrimString.cat ", " (list_to_string_helper xs))
    end.

  Definition list_to_string (l : list nat) : PrimString.string :=
    PrimString.cat "[ " (PrimString.cat (list_to_string_helper l) " ]").

  Definition input_lst1 := [ 212498;127;5981;2749812;74879;126;4;51;2412;10645 ].

  Definition test_quicksort_fun (_ : unit) : PrimString.string :=
    let out := quicksort_fun input_lst1 in
    list_to_string out.

End QuicksortFun.

Require Import Crane.Mapping.NatIntStd.


Crane Extract Inlined Constant QuicksortFun.int_to_string => "std::to_string(%a0)".

Set Crane Loopify.
Crane Extraction "loopification_quicksort_bug" QuicksortFun.test_quicksort_fun.
