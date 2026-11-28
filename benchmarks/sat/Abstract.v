(** The abstract solver state the proofs reason about.

    [Repr.repr] relates a pair of [Global] stores to an [astate]:
    - [db] is the clause database in arena order; clause [k] sits at the
      arena offset [off db k] (the arena holds [enc db], then spare room);
    - [wl] is, per literal, its watch list as clause {i indices};
    - [fv f] is the contents of the [nat] array of field [f], except that
      the trail, the trail limits and the learnt clause are cut to their
      lengths, and reasons name clauses by index: [S k] is clause [k].

    Clause indices rather than offsets keep the invariants ([Inv]) about
    lists of clauses; [Repr] translates. *)
From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

(** The [nat]-array fields of the solver state, so that [fv] treats them
    uniformly. *)
Inductive fld := FAsg | FLvl | FRsn | FPh | FSt | FSn | FTr | FLim | FMisc | FLrn.

(** Boolean equality on field names; [fset] uses it to pick the field. *)
Definition fld_eqb (f g : fld) : bool :=
  match f, g with
  | FAsg, FAsg | FLvl, FLvl | FRsn, FRsn | FPh, FPh | FSt, FSt | FSn, FSn
  | FTr, FTr | FLim, FLim | FMisc, FMisc | FLrn, FLrn => true
  | _, _ => false
  end.

(** [fld_eqb] reflects equality. *)
Lemma fld_eqb_eq f g : fld_eqb f g = true <-> f = g.
Proof. destruct f, g; cbn; split; congruence. Qed.

(** The updated field itself. *)
Lemma fld_eqb_refl f : fld_eqb f f = true.
Proof. now apply fld_eqb_eq. Qed.

(** The abstract state. *)
Record astate := AS {
  db : list (list nat);   (** the clauses, in arena order *)
  wl : list (list nat);   (** per literal: the indices of the clauses watching it *)
  fv : fld -> list nat    (** the contents of each field *)
}.

(** Replace the contents of field [f]. *)
Definition fset (st : astate) (f : fld) (xs : list nat) : astate :=
  AS (db st) (wl st) (fun g => if fld_eqb g f then xs else fv st g).
(** Replace the clauses: a write into the arena. *)
Definition dset (st : astate) (d : list (list nat)) : astate := AS d (wl st) (fv st).
(** Replace the watch lists. *)
Definition wset (st : astate) (w : list (list nat)) : astate := AS (db st) w (fv st).
(** Append clause [cl]: a learnt clause stored at the end of the arena. *)
Definition cpush (st : astate) (cl : list nat) : astate := AS (db st ++ [cl]) (wl st) (fv st).

(** Reading back the field just set. *)
Lemma fv_fset_eq st f xs : fv (fset st f xs) f = xs.
Proof. cbn. now rewrite fld_eqb_refl. Qed.

(** The flat arena encoding of clauses: each its length, then its literals. *)
Definition enc (D : list (list nat)) : list nat := concat (map (fun c => length c :: c) D).

(** The arena offset of clause [k] of [D]. *)
Definition off (D : list (list nat)) (k : nat) : nat := length (enc (firstn k D)).

(** * Lists updated in place *)

(** [xs] with position [i] replaced by [x]; out of range, [xs]. *)
Fixpoint lset {A} (xs : list A) (i : nat) (x : A) : list A :=
  match xs, i with
  | [], _ => []
  | _ :: xs', O => x :: xs'
  | y :: xs', S i' => y :: lset xs' i' x
  end.

(** [lset] never changes the length. *)
Lemma lset_length {A} (xs : list A) i x : length (lset xs i x) = length xs.
Proof. revert i; induction xs; destruct i; cbn; auto. Qed.

(** An in-bounds [lset] is read back at its index. *)
Lemma nth_error_lset_eq {A} (xs : list A) i x : i < length xs -> nth_error (lset xs i x) i = Some x.
Proof. revert i; induction xs; destruct i; cbn; intros; try lia; auto. apply IHxs; lia. Qed.

(** [lset] leaves the other indices alone. *)
Lemma nth_error_lset_neq {A} (xs : list A) i j x : i <> j -> nth_error (lset xs i x) j = nth_error xs j.
Proof. revert i j; induction xs; destruct i, j; cbn; intros; auto; congruence. Qed.

(** A read after [lset], by cases; out of bounds [lset] is a no-op. *)
Lemma nth_error_lset {A} (xs : list A) i j x :
  nth_error (lset xs i x) j = if Nat.eqb i j then (if Nat.ltb i (length xs) then Some x else None)
                              else nth_error xs j.
Proof.
  destruct (Nat.eqb_spec i j) as [<- | Hne].
  - destruct (Nat.ltb_spec i (length xs)).
    + now apply nth_error_lset_eq.
    + apply nth_error_None. rewrite lset_length. lia.
  - now apply nth_error_lset_neq.
Qed.

(** [nth_error_lset] for [nth] with a default. *)
Lemma nth_lset {A} (xs : list A) i j x d :
  nth j (lset xs i x) d = if Nat.eqb i j then (if Nat.ltb i (length xs) then x else d) else nth j xs d.
Proof.
  destruct (Nat.ltb_spec j (length xs)).
  - assert (Hj : j < length (lset xs i x)) by (now rewrite lset_length).
    pose proof (nth_error_lset xs i j x) as E.
    rewrite (nth_error_nth' _ d Hj), (nth_error_nth' _ d H) in E.
    destruct (Nat.eqb i j), (Nat.ltb i (length xs)); congruence.
  - rewrite !nth_overflow; try (rewrite ?lset_length; lia).
    destruct (Nat.eqb_spec i j), (Nat.ltb_spec i (length xs)); auto; lia.
Qed.

(** A write past the prefix [xs] lands in the suffix. *)
Lemma lset_app_r {A} (xs ys : list A) i x :
  length xs <= i -> lset (xs ++ ys) i x = xs ++ lset ys (i - length xs) x.
Proof.
  revert i; induction xs as [|a xs IH]; intros i Hi; cbn.
  - now rewrite Nat.sub_0_r.
  - destruct i; [cbn in Hi; lia|]. cbn. f_equal. apply IH. cbn in Hi. lia.
Qed.
