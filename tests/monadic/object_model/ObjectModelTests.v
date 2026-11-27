(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An object model using ST references for mutable state: objects are
    records of methods closing over their references (after OOHaskell,
    https://github.com/nkaretnikov/OOHaskell/blob/master/samples/SimpleST.hs).
    The account invariant -- the balance is never negative -- holds after
    construction and is preserved by every method ([spec] lemmas). *)

From Stdlib Require Import
  Arith.PeanoNat
  Lia
  ZArith
.

From ITree Require Import
  Events.Exception
  ITree
  ITreeFacts
.

From Crane Require Monads.ST.
From Crane Require Import
  Monads.ITree
  Monads.Error
  Monads.STFacts
  Monads.STSpec
  Extraction.

Import Monads.
Local Open Scope monad_scope.

Section Classes.

  Context {R : ST.Refs}.
  Notation V := (fun _ : nat => Z).
  Notation E0 := (ST.Event R V +' exceptE Err).

  Local Notation "x :== y" := (ST.write_ref x y) (at level 0).
  Local Notation "! x" := (ST.read_ref x) (at level 50).

  Record Point := mkPoint {
      getX : unit -> itree E0 Z;
      moveD : Z -> itree E0 unit;
      offsetX : unit -> itree E0 Z;
    }.

  Definition class_pointST (init : Z) : itree E0 Point :=
    ref <- ST.new_ref init;;
    let moveD :=
      fun move_amt =>
        i <- ST.read_ref ref;;
        ST.write_ref ref (i + move_amt)%Z in
    let offsetX :=
      i <- ST.read_ref ref;;
      Ret (i - init)%Z in
    Ret (mkPoint (fun _ => ST.read_ref ref) moveD (fun _ => offsetX)).

  Definition testtoST1 : itree E0 (Z * Z * Z) :=
    p <- class_pointST 1;;
    a <- getX p tt;;
    moveD p 2;;
    b <- getX p tt;;
    c <- offsetX p tt;;
    Ret (a,b,c).

  Definition testtoST2 : itree E0 (Z * Z * Z * Z) :=
    p1 <- class_pointST 1;;
    p2 <- class_pointST 10;;
    a <- getX p1 tt;;
    b <- getX p2 tt;;
    (* reading from one and putting into the other *)
    v1 <- getX p1 tt;; moveD p2 v1;;
    c <- getX p1 tt;;
    d <- getX p2 tt;;
    Ret (a,b,c,d).

  Record Account := mkAccount {
      getBalance : unit -> itree E0 Z;
      deposit : nat -> itree E0 Z;
      withdraw : Z -> itree E0 (option Z);
    }.

  Definition getBalance_imp (ref : ST.ref Z) : unit -> itree E0 Z :=
    fun _ => ST.read_ref ref.

  Definition deposit_imp (ref : ST.ref Z) : nat -> itree E0 Z :=
    fun amt : nat =>
      bal <- ST.read_ref ref;;
      let new_bal := (bal + (Z.of_nat amt))%Z in
      ST.write_ref ref new_bal;;
      Ret new_bal.

  Definition withdraw_imp (ref : ST.ref Z) : Z -> itree E0 (option Z) :=
    fun amt : Z =>
      bal <- ST.read_ref ref;;
      let new_bal := (bal - amt)%Z in
      if (new_bal <? 0)%Z then
        Ret None
      else
        ST.write_ref ref new_bal;;
        Ret (Some new_bal).

  Definition class_Account (init : Z) : itree E0 Account :=
    bal_ref <- ST.new_ref init;;
    Ret
      {| getBalance _ := !bal_ref;
         deposit amt :=
            bal <- !bal_ref;;
            let new_bal := (bal + (Z.of_nat amt))%Z in
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
    acc <- class_Account 100;;
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
    acc1 <- class_Account 100;;
    acc2 <- class_Account 150;;
    a <- getBalance acc1 tt;;
    result <- withdraw acc1 a;;
    match result with
    | Some 0%Z => (* withdrawal succeeds, transfer money*)
        b <- deposit acc2 (Z.to_nat a);;
        c <- getBalance acc1 tt;;
        Ret (a,true,b,c)
    | _ => (* withdrawal failed, do nothing, return balance of a,b *)
        b <- getBalance acc2 tt;;
        c <- getBalance acc1 tt;;
        Ret (a,false,b,c)
    end.

  Record BankAccountCollection :=
    mkBankAccount {
      checking : Account;
      saving   : Account;
    }.

  Definition class_BankAccount (init_checking init_saving : Z) : itree E0 BankAccountCollection :=
    checking' <- class_Account init_checking;;
    saving' <- class_Account init_saving;;
    Ret
      {| checking := checking';
         saving := saving';
      |}.

  (* Fully transfer amounts between two accounts *)
  Definition testBankAccount1 : itree E0 (Z * bool * Z * Z) :=
    acc <- class_BankAccount 100 150;;
    a <- getBalance (checking acc) tt;;
    result <- withdraw (checking acc) a;;
    match result with
    | Some 0%Z => (* withdrawal succeeds, transfer money*)
        b <- deposit (saving acc) (Z.to_nat a);;
        c <- getBalance (checking acc) tt;;
        Ret (a,true,b,c)
    | _ => (* withdrawal failed, do nothing, return balance of a,b *)
        b <- getBalance (checking acc) tt;;
        c <- getBalance (saving acc) tt;;
        Ret (a,false,b,c)
    end.

End Classes.

(** * The account invariant *)

Section AccountProofs.

  Notation V := (fun _ : nat => Z).

  (** [acc]'s methods are those of the reference [ref]. *)
  Record account_impl (ref : nat) (acc : @Account ST.model_refs) :=
    mkAccountImpl {
        getBalance_impld_by : getBalance acc = getBalance_imp (R := ST.model_refs) ref;
        withdraw_impld_by : withdraw acc = withdraw_imp (R := ST.model_refs) ref;
        deposit_impld_by : deposit acc = deposit_imp (R := ST.model_refs) ref;
      }.

  (** [acc] is backed by [ref], which holds a balance that is not negative. *)
  Definition account_wf (acc : @Account ST.model_refs) (ref : nat) (m : ST.mem V) : Prop :=
    account_impl ref acc /\ exists v, read_at (V := V) ref m = Some v /\ (v >= 0)%Z.

  Lemma class_account_is_wf (init : Z) (m : ST.mem V) :
    (init >= 0)%Z ->
    spec (E := exceptE Err) (class_Account (R := ST.model_refs) init) m
      (fun m' acc => exists ref, account_wf acc ref m').
  Proof.
    intros Hinit. unfold class_Account.
    apply spec_bind, new_ref. cbv beta. apply spec_ret.
    exists (ST.fresh m). split; [ constructor; reflexivity |].
    exists init. split; [ apply read_at_write_at_eq | exact Hinit ].
  Qed.

  Lemma withdraw_preserves_wf (acc : @Account ST.model_refs) ref amt (m : ST.mem V) :
    account_wf acc ref m ->
    spec (E := exceptE Err) (withdraw acc amt) m (fun m' _ => account_wf acc ref m').
  Proof.
    intros [[Hget Hwdrw Hdep] (v & Hv & Hpos)]. rewrite Hwdrw. unfold withdraw_imp.
    apply spec_bind. eapply read_ref; [ exact Hv |]. cbv beta.
    destruct (v - amt <? 0)%Z eqn:Hneg.
    - apply spec_ret. split; [ constructor; assumption |]. exists v. auto.
    - apply spec_bind, write_ref. cbv beta. apply spec_ret.
      split; [ constructor; assumption |]. exists (v - amt)%Z.
      split; [ apply read_at_write_at_eq |]. apply Z.ltb_ge in Hneg. lia.
  Qed.

  Lemma deposit_preserves_wf (acc : @Account ST.model_refs) ref amt (m : ST.mem V) :
    account_wf acc ref m ->
    spec (E := exceptE Err) (deposit acc amt) m (fun m' _ => account_wf acc ref m').
  Proof.
    intros [[Hget Hwdrw Hdep] (v & Hv & Hpos)]. rewrite Hdep. unfold deposit_imp.
    apply spec_bind. eapply read_ref; [ exact Hv |]. cbv beta.
    apply spec_bind, write_ref. cbv beta. apply spec_ret.
    split; [ constructor; assumption |]. exists (v + Z.of_nat amt)%Z.
    split; [ apply read_at_write_at_eq | lia ].
  Qed.

  Lemma getBalance_preserves_wf (acc : @Account ST.model_refs) ref (m : ST.mem V) :
    account_wf acc ref m ->
    spec (E := exceptE Err) (getBalance acc tt) m (fun m' _ => account_wf acc ref m').
  Proof.
    intros [[Hget Hwdrw Hdep] (v & Hv & Hpos)]. rewrite Hget. unfold getBalance_imp.
    eapply read_ref; [ exact Hv |].
    split; [ constructor; assumption |]. exists v. auto.
  Qed.

End AccountProofs.

(** * The examples, run in the model *)

Transparent HAList.halist_lookup HAList.halist_add
            HAList.HMap_halist HAList.HMapOk_halist.

Definition run_test1 : itree (exceptE Err) (Z * Z * Z) := ST.run (fun R => testtoST1 (R := R)).

Lemma point_run_burn1 : burn 100 run_test1 = Ret (1, 3, 2)%Z.
Proof. lazy. reflexivity. Qed.

Definition run_test2 : itree (exceptE Err) (Z * Z * Z * Z) := ST.run (fun R => testtoST2 (R := R)).

Lemma point_run_burn2 : burn 100 run_test2 = Ret (1, 10, 1, 11)%Z.
Proof. lazy. reflexivity. Qed.

Definition run_acc1 : itree (exceptE Err) (Z * Z * bool * Z) := ST.run (fun R => testAccount1 (R := R)).

Lemma acc_run_burn1 : burn 100 run_acc1 = Ret (100, 150, false, 150)%Z.
Proof. lazy. reflexivity. Qed.

Definition run_acc2 : itree (exceptE Err) (Z * bool * Z * Z) := ST.run (fun R => testAccount2 (R := R)).

Lemma acc_run_burn2 : burn 100 run_acc2 = Ret (100, true, 250, 0)%Z.
Proof. lazy. reflexivity. Qed.

Definition run_bank_acc1 : itree (exceptE Err) (Z * bool * Z * Z) :=
  ST.run (fun R => testBankAccount1 (R := R)).

Lemma bank_acc_run_burn1 : burn 100 run_bank_acc1 = Ret (100, true, 250, 0)%Z.
Proof. lazy. reflexivity. Qed.

From Crane Require Import Mapping.ZInt Mapping.NatIntStd.

Definition testtoST1_ext :=
  Eval unfold testtoST1, class_pointST in (@testtoST1 ST.cpp_refs).
Definition testtoST2_ext :=
  Eval unfold testtoST2, class_pointST in (@testtoST2 ST.cpp_refs).

Definition acc_test1_ext :=
  Eval unfold testAccount1, class_Account in (@testAccount1 ST.cpp_refs).

Definition acc_test2_ext :=
  Eval unfold testAccount2, class_Account in (@testAccount2 ST.cpp_refs).

Definition bankacc_test1_ext :=
  Eval unfold testBankAccount1, class_BankAccount, class_Account in (@testBankAccount1 ST.cpp_refs).

Crane Extraction "object_model"
  testtoST1_ext
  testtoST2_ext
  acc_test1_ext
  acc_test2_ext
  bankacc_test1_ext
.
