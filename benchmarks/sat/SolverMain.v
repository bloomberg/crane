(** The top-level theorem: what [Solver.solve_dimacs], the function the
    drivers call, guarantees about the bytes of any file.

    From any finite heap in which [bytes] holds [bs], no run of
    [solve_dimacs] gets stuck (every event is in bounds and on a live
    handle; giving up with [VAbort] is allowed), and if it finishes with
    [r] then [answer bs r]: the answer is exactly right about whether [bs]
    is a DIMACS CNF file ([DimacsSpec.dimacs]), and whenever it says SAT or
    UNSAT it is right about the formula the file spells.  Termination is
    not claimed; the step budget makes the answer 2 ("unknown") instead. *)
From Stdlib Require Import List PeanoNat Lia.
From Crane Require Import Monads.ITree.
Require Import SatVec VecSem VecSafe Solver SolverSat SolverUnsat SolverSafe DimacsSpec.
Import ListNotations.
Import Solver.

Local Notation cellof := (fun T : Type => list T).

(** What the result [r] of [solve_dimacs] says about the file [bs]. *)
Definition answer (bs : list nat) (r : nat) : Prop :=
  match r mod 8 with
  | 0 => exists F, dimacs bs F /\ ~ exists val, satisfies val F    (* UNSAT *)
  | 1 => exists F, dimacs bs F /\ exists val, satisfies val F      (* SAT *)
  | 2 | 3 => exists F, dimacs bs F             (* out of budget; model check failed *)
  | 4 => ~ exists F, dimacs bs F               (* not a DIMACS CNF file *)
  | _ => False
  end.

(** * Reading the bytes and writing the clauses *)

Lemma firstn_snoc {A} (xs : list A) i x : nth_error xs i = Some x -> firstn (S i) xs = firstn i xs ++ [x].
Proof.
  revert i; induction xs as [|y xs IH]; intros [|i] H; cbn in *; try discriminate.
  - now injection H as ->.
  - f_equal. now apply IH.
Qed.

Lemma read_bytes_safe bytes bs : forall i acc Q h,
  h (vloc bytes) = Some (existT cellof nat bs) -> i <= length bs ->
  Q (firstn i bs ++ acc) h -> safe (read_bytes bytes i acc) Q h.
Proof.
  induction i as [|i IH]; intros acc Q h Hb Hi HQ; cbn [read_bytes].
  - apply safe_ret. exact HQ.
  - apply safe_bind. eapply safe_vget; [exact Hb | lia |]. intros b Hnb.
    apply IH; [exact Hb | lia |]. rewrite (firstn_snoc _ _ _ Hnb), <- app_assoc in HQ. exact HQ.
Qed.

(** The flat encoding [write_cnf] produces. *)
Definition enc (F : list (list nat)) : list nat := concat (map (fun c => length c :: c) F).

Lemma tlen_eq {A} (l : list A) n : tlen l n = n + length l.
Proof. revert n; induction l as [|x l IH]; intros n; cbn; [lia | rewrite IH; lia]. Qed.

Lemma write_lits_safe input : forall c xs Q h,
  h (vloc input) = Some (existT cellof nat xs) ->
  (forall h', h' (vloc input) = Some (existT cellof nat (xs ++ c)) -> Q tt h') ->
  safe (write_lits input c) Q h.
Proof.
  induction c as [|l c IH]; intros xs Q h Hi HQ; cbn [write_lits].
  - apply safe_ret, HQ. now rewrite app_nil_r.
  - apply safe_bind. eapply safe_vpush; [exact Hi |]. apply IH with (xs := xs ++ [l]); [apply upd_eq |].
    intros h' Hh'. apply HQ. now rewrite <- app_assoc in Hh'.
Qed.

Lemma write_cnf_safe input : forall F xs pos Q h,
  h (vloc input) = Some (existT cellof nat xs) ->
  (forall h', h' (vloc input) = Some (existT cellof nat (xs ++ enc F)) -> Q (pos + length (enc F)) h') ->
  safe (write_cnf input F pos) Q h.
Proof.
  induction F as [|c F IH]; intros xs pos Q h Hi HQ; cbn [write_cnf].
  - apply safe_ret. replace (pos + length (enc [])) with pos in HQ by (cbn; lia).
    apply HQ. cbn. now rewrite app_nil_r.
  - cbv zeta. rewrite tlen_eq. cbn [Nat.add].
    apply safe_bind. eapply safe_vpush; [exact Hi |].
    apply safe_bind. eapply write_lits_safe; [apply upd_eq |]. intros h1 Hh1.
    apply IH with (xs := (xs ++ [length c]) ++ c); [exact Hh1 |]. intros h' Hh'.
    replace (pos + 1 + length c + length (enc F)) with (pos + length (enc (c :: F))) by
      (unfold enc; cbn; rewrite length_app; cbn; lia).
    apply HQ. unfold enc in *. cbn. now rewrite <- !app_assoc in Hh'.
Qed.

Lemma enc_encodes : forall F pre, encodes (pre ++ enc F) (length pre + length (enc F)) (length pre) F.
Proof.
  induction F as [|c F IH]; intros pre.
  - apply enc_nil. unfold enc. cbn. lia.
  - unfold enc. cbn [map concat]. fold (enc F). apply enc_cons.
    + cbn. lia.
    + rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
    + intros j Hj. rewrite nth_error_app2 by lia. replace (length pre + 1 + j - length pre) with (S j) by lia.
      cbn. rewrite nth_error_app1 by exact Hj. reflexivity.
    + specialize (IH (pre ++ length c :: c)). rewrite <- app_assoc, length_app in IH. cbn [length] in IH.
      replace (length pre + length ((length c :: c) ++ enc F)) with (length pre + S (length c) + length (enc F))
        by (rewrite length_app; cbn; lia).
      replace (length pre + 1 + length c) with (length pre + S (length c)) by lia.
      exact IH.
Qed.

(** * The theorem *)

Theorem solve_dimacs_correct fuel budget bytes bs h0 :
  h0 (vloc bytes) = Some (existT cellof nat bs) ->
  safe (Solver.solve_dimacs fuel budget bytes) (fun r _ => answer bs r) h0.
Proof.
  intros Hb. unfold solve_dimacs.
  apply safe_bind. eapply safe_vlen; [exact Hb |].
  apply safe_bind. eapply read_bytes_safe; [exact Hb | lia |].
  rewrite firstn_all, app_nil_r.
  destruct (parse bs) as [[nvars F] |] eqn:Hp.
  2: { apply safe_ret. unfold answer. cbn. now apply parse_none. }
  destruct (parse_sound _ _ _ Hp) as (HD & HB & _).
  apply safe_bind, safe_vmake. intros input Hin.
  apply safe_bind. eapply write_cnf_safe; [apply upd_eq |]. intros h1 Hi1. cbn [repeat app] in Hi1.
  pose proof (enc_encodes F []) as HE. cbn [app length] in HE.
  pose proof (run_safe fuel budget nvars input _ _ F h1 Hi1 HE HB) as Hs.
  assert (Hw : wp (Solver.run fuel budget nvars input (0 + length (enc F)))
                  (fun r _ => (r mod 8 = 1 -> exists val, satisfies val F) /\
                              (r mod 8 = 0 -> ~ exists val, satisfies val F)) h1).
  { intros r h2 Hrun. split.
    - intros Hr1. eapply run_sat_sound; [exact Hi1 | exact HE | exact Hrun | exact Hr1].
    - intros Hr0. eapply run_unsat_sound; [exact Hi1 | exact HE | exact Hrun | exact Hr0]. }
  eapply safe_conseq; [exact (safe_and_wp _ _ _ _ Hs Hw) |].
  intros r h2 (Hle & Hs1 & Hs0). cbv beta. unfold answer.
  destruct (r mod 8) as [|[|[|[|]]]] eqn:E; try lia; eauto.
Qed.
