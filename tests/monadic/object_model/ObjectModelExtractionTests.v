(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* An object model using STRefs for mutable state *)



From Stdlib Require Import
  Arith.PeanoNat
  Arith.Peano_dec
  Init.Peano
  Lia
  List
  Morphisms
  RelationClasses
  Relation_Definitions
  Setoid
  Strings.String
  Classes.EquivDec
  Basics
  ZArith
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


From ITree Require Import
  Events.Exception
  Events.FailFacts
  Events.MapDefault
  Events.MapDefaultFacts
  Events.State
  Events.StateFacts
  ITree
  ITreeFacts
.
            

From Crane Require Import
  Monads.ITree
  Monads.Error
  Monads.Indices
  Monads.STMonad
  Monads.STMonadFacts
  Monads.MonadFacts
  Utils.HMap
  Utils.HAList
  Extraction.

Section PointDef.


  Context (S : Type).
  Let T := nat.
  Let ltu := Nat.le.
  Let V : T -> Type := fun _ => Z.
  Let E0 := (STEvent T S V) +' exceptE Err.

  Local Notation ref := (newSTRef).
  Local Notation "x :== y" := (writeSTRef x y) (at level 0).
  Local Notation "! x" := (readSTRef x) (at level 50).
  

  Record Point := mkPoint {
      getX : unit -> itree E0 Z;
      moveD : Z -> itree E0 unit;
      offsetX : unit -> itree E0 Z;
    }.


  
  (* NOTE: might wanna enforce unique indices with a global effect
           draw indices from a index generator. *)
  (* Modeling off of examples in OOHaskell, starting from https://github.com/nkaretnikov/OOHaskell/blob/master/samples/SimpleST.hs#L69 *)
  Definition class_pointST {idx : T} (init : Z) : itree E0 Point :=
    ref <- newSTRef 0 init ;;
    let moveD :=
      fun move_amt =>
        i <- readSTRef ref;;
        writeSTRef ref (i + move_amt)%Z in
    let offsetX :=
      i <- readSTRef ref;;
      Ret (i - init)%Z in
    Ret (mkPoint (fun _ => readSTRef ref) moveD (fun _ => offsetX)).


  Definition testtoST1 : itree E0 (Z * Z * Z) :=
    p <- @class_pointST 0 1;;
    a <- getX p tt;;
    moveD p 2;;
    b <- getX p tt;;
    c <- offsetX p tt;;
    Ret (a,b,c).


  Definition testtoST2 : itree E0 (Z * Z * Z * Z) :=
      p1 <- @class_pointST 0 1;;
      p2 <- @class_pointST 1 10;;
      a <- getX p1 tt;;
      b <- getX p2 tt;;
	    (* reading from one and putting into the other *)
      v1 <- getX p1 tt;; moveD p2 v1;;
      c <- getX p1 tt;;
      d <- getX p2 tt;;
      Ret (a,b,c,d)
  .

  
  Record Account := mkAccount {
      getBalance : unit -> itree E0 Z;
      deposit : Z -> itree E0 Z;
      withdraw : Z -> itree E0 (option Z);
    }.

  Definition getBalance_imp (idx : T) (ref : STRef S Z) : unit -> itree E0 Z :=
    fun _ => readSTRef (idx := idx) ref.

  Definition deposit_imp (idx : T) (ref : STRef S Z) : Z -> itree E0 Z :=
    fun amt : Z =>
      bal <- readSTRef (idx := idx) ref;;
      let new_bal := (bal + amt)%Z in
      writeSTRef (idx := idx) ref new_bal;;
      Ret new_bal.

  Definition withdraw_imp (idx : T) (ref : STRef S Z) : Z -> itree E0 (option Z) :=
      fun amt : Z =>
        bal <- readSTRef (idx := idx) ref;;
        let new_bal := (bal - amt)%Z in
        if (new_bal <? 0)%Z then
          Ret None
        else
          writeSTRef (idx := idx) ref new_bal;; 
          Ret (Some new_bal).


  Definition class_Account (idx : T) (init : Z) : itree E0 Account :=
    bal_ref <- ref idx init ;;
    Ret
      {| getBalance _ := !bal_ref;
         deposit amt := 
            bal <- !bal_ref;;
            let new_bal := (bal + amt)%Z in
             bal_ref :== new_bal;;
             Ret new_bal;
        withdraw amt := 
            bal <- !bal_ref;;
            let new_bal := (bal - amt)%Z in
            if (new_bal <? 0)%Z then
              Ret None
            else
              bal_ref :== new_bal;; 
              Ret (Some new_bal);
      |}.


  Definition testAccount1 : itree E0 (Z * Z * bool * Z) :=
    acc <- @class_Account 0%nat 100;;
    a <- getBalance acc tt;;
    b <- deposit acc 50;; (* deposit 50 *)
    c <- withdraw acc 160;; (* attempt to withdraw more than we can *)
    d <- getBalance acc tt;; (* read final value *)
    let c_is_Some :=
      match c with
      | Some _ => true
      | None => false
      end in
    Ret (a,b,c_is_Some,d).

  (* Fully transfer amounts between two accounts *)
  Definition testAccount2 : itree E0 (Z * bool * Z * Z) :=
    acc1 <- @class_Account 0%nat 100;;
    acc2 <- @class_Account 0%nat 150;;
    a <- getBalance acc1 tt;;
    result <- withdraw acc1 a;;
    match result with
    | Some 0%Z => (* withdrawal succeeds, transfer money*)
        b <- deposit acc2 a;;
        c <- getBalance acc1 tt;;
        Ret (a,true,b,c)
    | _ => (* withdrawal failed, do nothing, return balance of a,b *)
        b <- getBalance acc2 tt;;
        c <- getBalance acc1 tt;;
        Ret (a,false,b,c)
    end.

  #[export] Instance hmap_nat_v : HMap (@idx_key T T) (idx_key_type V) mem :=
    HMap_halist (idx_key T) (idx_key_type V).


  (* TODO: make this a structure instead of `and` *)


  Definition backed_by (acc : Account) (idx : T) (ref : STRef S Z) : Prop :=
    getBalance acc = getBalance_imp idx ref /\
    withdraw acc = withdraw_imp idx ref /\
    deposit acc = deposit_imp idx ref.


  Definition account_wf (acc : Account) (idx : T) (ref : STRef S Z)
    (m : @mem T V)  : Prop :=
    backed_by acc idx ref /\
    exists v, HMap.lookup (STRefToIx S Z ref, idx) m = Some v /\ (v >= 0)%Z.

  Definition max_idx (m : @mem T V) :=
    Datatypes.S (fold (fun '(existT _ (n, _) _) (acc : nat) => Nat.max n acc) 0%nat m).

  Opaque HAList.halist_lookup HAList.halist_add
        HAList.HMap_halist HAList.HMapOk_halist.

  Lemma interp_st_class_account : forall
    (init : Z)
    (idx : T)
    (l : @mem T V),
      interp_st ltu (Account) (@class_Account idx init) l
        ≈
    ITreeDefinition.Ret
    (HMap.add (max_idx l, idx)
         init l,
     {|
       getBalance := getBalance_imp idx (MkSTRef S (V 0%nat) (max_idx l));
       deposit := deposit_imp idx (MkSTRef S (V 0%nat) (max_idx l));
       withdraw := withdraw_imp idx (MkSTRef S (V 0%nat) (max_idx l))
     |}).
    Proof using Type.
      intros init idx l.
      unfold class_Account.
      change T with nat in *.
      unfold E0.
      rewrite interp_st_bind.
      unfold newSTRef. rewrite interp_st_trigger. cbn.
      change_to_monad.
      change (V _) with Z in *.
      monad_simpl_inner.
      change_to_monad.
      rewrite interp_st_ret.
      unfold max_idx.
      unfold getBalance_imp,deposit_imp,withdraw_imp.
      change_to_monad.
      reflexivity.
    Qed.


    

  Lemma class_account_is_wf : forall (acc : Account) (idx : T) (mem mem2 : @mem T V ) (init : Z),
      (init >= 0)%Z ->
      interp_st ltu _ (@class_Account idx init) mem ≈ Ret (mem2, acc) ->
      exists ref, account_wf acc idx ref mem2. 
    Proof using Type.
      intros.
      unfold account_wf.
      rewrite interp_st_class_account in H0.
      eapply eutt_inv_Ret in H0.
      inversion H0.
      unfold getBalance. unfold getBalance_imp in *.
      unfold readSTRef.
      exists (MkSTRef S (V 0) (max_idx mem)).
      split. 
      - econstructor.
        + econstructor.
        + split; reflexivity.
      - exists init. 
        split.
        + eapply st_lookup_add_eq. 
        + assumption.
    Qed.
      
    Local Ltac unfold_instances :=
      change T with nat in *;
      unfold E0 in *;
      unfold V in *.

  Lemma withdraw_cannot_return_negative :
    forall (acc : Account) (idx : T) (ref : STRef S Z) (amt new_bal : Z) (m0 m1 : @mem T V) (o : option Z),
      account_wf acc idx ref m0 ->
      interp_st ltu _ (withdraw acc amt) m0 ≈ Ret (m1 , o) ->
      account_wf acc idx ref m1.
    Proof using Type. 
      intros acc idx ref amt b m0 m1 o Hwdrw Hintrp.
      unfold account_wf in *. destruct Hwdrw as [Hback Hlookup].
      split. try assumption.
      unfold backed_by in Hback. destruct Hback as [Hgetb [Hwdrw Hdepos]].
      rewrite Hwdrw in Hintrp.
      unfold withdraw_imp in Hintrp. unfold_instances.
      rewrite interp_st_bind in Hintrp.
      unfold readSTRef in Hintrp.
      rewrite interp_st_trigger in Hintrp. cbn in Hintrp.
      destruct Hlookup as [v [Hlookup Hvnz]].
      change (lookup (STRefToIxNat S Z ref, idx) m0) with (lookup (STRefToIx S Z ref, idx) m0) in Hintrp. 
      replace (lookup (STRefToIx S Z ref, idx) m0) with
              (Some v) in Hintrp.
      change (@ITree.bind ?E) with (@Monad.bind (itree E) _) in Hintrp.
      setoid_rewrite Ret_is_ret in Hintrp.
      repeat (repeat setoid_rewrite Monad.bind_bind in Hintrp;
          repeat setoid_rewrite bind_Ret_l in Hintrp;
          repeat setoid_rewrite bind_Ret_r in Hintrp).
      destruct (v - amt <? 0)%Z eqn:Hv.
      setoid_rewrite Ret_is_ret in Hintrp.
      rewrite interp_st_ret in Hintrp.
      eapply eutt_inv_Ret in Hintrp. inversion Hintrp. subst.
      exists v. split; assumption.
      exists (v - amt)%Z.
      unfold_instances.
      change (@Monad.bind (itree ?E) _) with (@ITree.bind E) in Hintrp.
      rewrite interp_st_bind_eutt in Hintrp.
      unfold writeSTRef in Hintrp.
      rewrite interp_st_trigger in Hintrp. cbn in Hintrp.
      change (@ITree.bind ?E) with (@Monad.bind (itree E) _) in Hintrp.
      setoid_rewrite bind_Ret_l in Hintrp.
      cbv beta iota in Hintrp.
      unfold Ret in Hintrp.
      rewrite interp_st_Ret in Hintrp.
      eapply eutt_inv_Ret in Hintrp.
      inversion Hintrp. subst. split.
      - eapply st_lookup_add_eq.
      - lia.  
     Qed.


  Lemma deposit_preserves_wf :
    forall (acc : Account) (idx : T) (ref : STRef S Z) (amt new_bal : Z) (m0 m1 : @mem T V) (out_val : Z),
      (amt >= 0)%Z ->
      account_wf acc idx ref m0 ->
      interp_st ltu _ (deposit acc amt) m0 ≈ Ret (m1 , out_val) ->
      account_wf acc idx ref m1.
    Proof using Type.
      intros acc idx ref amt b m0 m1 o Hamt Hwdrw Hintrp.
      unfold account_wf in *. destruct Hwdrw as [Hback Hlookup].
      split; try assumption.
      unfold backed_by in Hback. destruct Hback as [Hgetb [Hwdrw Hdepos]].
      rewrite Hdepos in Hintrp. unfold deposit_imp in Hintrp. unfold_instances.
      rewrite interp_st_bind in Hintrp. unfold readSTRef in *. rewrite interp_st_trigger in Hintrp. cbn in Hintrp.  
      destruct Hlookup as [v [Hlookup Hvnz]].
      change (lookup (STRefToIxNat S Z ref, idx) m0) with (lookup (STRefToIx S Z ref, idx) m0) in Hintrp. 
      replace (lookup (STRefToIx S Z ref, idx) m0) with
              (Some v) in Hintrp.
      change (@ITree.bind ?E) with (@Monad.bind (itree E) _) in Hintrp.
      setoid_rewrite Ret_is_ret in Hintrp.
      repeat (repeat setoid_rewrite Monad.bind_bind in Hintrp;
          repeat setoid_rewrite bind_Ret_l in Hintrp;
          repeat setoid_rewrite bind_Ret_r in Hintrp).
      exists (v + amt)%Z. unfold_instances.
      change (@Monad.bind (itree ?E) _) with (@ITree.bind E) in Hintrp.
      rewrite interp_st_bind_eutt in Hintrp.
      unfold writeSTRef in Hintrp.
      rewrite interp_st_trigger in Hintrp. cbn in Hintrp.
      change (@ITree.bind ?E) with (@Monad.bind (itree E) _) in Hintrp.
      setoid_rewrite bind_Ret_l in Hintrp.
      cbv beta iota in Hintrp.
      unfold Ret in Hintrp.
      rewrite interp_st_Ret in Hintrp.
      eapply eutt_inv_Ret in Hintrp. inversion Hintrp. subst.
      split.
      - apply st_lookup_add_eq. 
      - lia.
    Qed.



  Lemma getBalance_preserves_wf :
    forall (acc : Account) (idx : T) (ref : STRef S Z) (out_val : Z) (m0 m1 : @mem T V),
      account_wf acc idx ref m0 ->
      interp_st ltu _ (getBalance acc tt) m0 ≈ Ret (m1 , out_val) ->
      account_wf acc idx ref m1.
    Proof.
      intros acc idx ref out_val m0 m1 Hwf Hintrp.
      destruct Hwf as [[Hgetbal [Hwth Hdep]] Hlookup]; rewrite Hgetbal in Hintrp.
      unfold getBalance_imp in Hintrp.
      unfold readSTRef in Hintrp.
      unfold_instances.
      rewrite interp_st_trigger in Hintrp; cbn in Hintrp.
      destruct Hlookup as [v [Hlookup Hv]].
      change (STRefToIxNat S Z ref, idx) with (STRefToIx S Z ref, idx) in Hintrp.
      rewrite Hlookup in Hintrp.
      eapply eutt_inv_Ret in Hintrp. inversion Hintrp. subst.
      split; try (repeat split; assumption). 
      exists out_val. split; try (repeat split; assumption).
    Qed.




                                            

End PointDef.


Transparent HAList.halist_lookup HAList.halist_add
            HAList.HMap_halist HAList.HMapOk_halist.
Existing Instance nat_ix_correct.
Existing Instance nat_ix_stref.

Definition run_test1 : itree (exceptE Err) (Z * Z * Z) :=
  runST (T := nat) (ltu := Nat.le) (V := fun _ : nat => Z) (S := unit) testtoST1.

Lemma point_run_burn1 : burn 100 run_test1 = Ret (1, 3, 2)%Z.
Proof. lazy. reflexivity. Qed.

Definition run_test2 : itree (exceptE Err) (Z * Z * Z * Z) :=
  runST (T := nat) (ltu := Nat.le) (V := fun _ : nat => Z) (S := unit) testtoST2.

Lemma point_run_burn2 : burn 100 run_test2 = Ret (1, 10, 1, 11)%Z.
Proof. lazy. reflexivity. Qed.

Definition run_acc1 : itree (exceptE Err) (Z * Z * bool * Z) :=
  runST (T := nat) (ltu := Nat.le) (V := fun _ : nat => Z) (S := unit) testAccount1.

Lemma acc_run_burn1 : burn 100 run_acc1 = Ret (100, 150, false, 150)%Z.
Proof. lazy. reflexivity. Qed.

Definition run_acc2 : itree (exceptE Err) (Z * bool * Z * Z) :=
  runST (T := nat) (ltu := Nat.le) (V := fun _ : nat => Z) (S := unit) testAccount2.

Lemma acc_run_burn2 : burn 100 run_acc2 = Ret (100, true, 250, 0)%Z.
Proof. lazy. reflexivity. Qed.






From Crane Require Import Mapping.ZInt.

Definition testtoST1_ext :=
  Eval unfold testtoST1, class_pointST in (testtoST1 unit).
Definition testtoST2_ext :=
  Eval unfold testtoST2, class_pointST in (testtoST2 unit).

Definition acc_test1_ext :=
  Eval unfold testAccount1, class_Account  in (testAccount1 unit).

Definition acc_test2_ext :=
  Eval unfold testAccount2, class_Account in (testAccount2 unit).

Crane Extraction "object_model" testtoST1_ext testtoST2_ext acc_test1_ext acc_test2_ext.









  



  
