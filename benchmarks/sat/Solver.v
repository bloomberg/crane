(** A CDCL SAT solver written directly in [itree vecE].

    Two-watched-literal propagation, first-UIP learning with
    non-chronological backjumping, phase saving, recency-ordered decisions
    and geometric restarts.  All mutable state lives in [vec]s, so every
    read and write is an event: Crane performs it in place, OCaml extraction
    builds a [Vis] node for it and hands it to the interpreter.

    Encoding: variable [v] has literals [2v] (positive) and [2v+1]
    (negative).  A variable's value is 0 (unassigned), 1 (true) or
    2 (false); a literal's value is read off the same three. *)
From Stdlib Require Import PeanoNat Bool.
Local Open Scope bool_scope.
From Crane Require Import Monads.ITree.
Require Import SatVec.

Module Solver.

Definition lvar (l : nat) : nat := Nat.div l 2.
Definition lneg (l : nat) : nat :=
  if Nat.eqb (Nat.modulo l 2) 0 then l + 1 else l - 1.
(** The literal of [v] that a value of [a] (1 or 2) makes true. *)
Definition lit_of (v a : nat) : nat := if Nat.eqb a 1 then 2 * v else 2 * v + 1.

Record state := mk_state {
  clauses : vec (vec nat);   (** clause database; a reason's implied literal is at 0 *)
  watches : vec (vec nat);   (** per literal: the clauses watching it at 0 or 1 *)
  assigns : vec nat;         (** per variable: 0, 1 or 2 *)
  level : vec nat;           (** per variable: decision level of its assignment *)
  reason : vec nat;          (** per variable: clause index + 1, or 0 for none *)
  phase : vec nat;           (** per variable: the value it last had *)
  stamp : vec nat;           (** per variable: conflict count when last bumped *)
  seen : vec nat;            (** per variable: scratch for [analyze] *)
  trail : vec nat;           (** assigned literals, in order *)
  trail_lim : vec nat;       (** per decision level: trail length at its decision *)
  misc : vec nat             (** 0: queue head, 1: conflicts, 2: restart limit,
                                 3: conflicts since restart *)
}.

Definition QHEAD := 0.
Definition CONFLICTS := 1.
Definition RLIMIT := 2.
Definition RCOUNT := 3.

Section Ops.
Variable s : state.

Definition lit_value (l : nat) : itree vecE nat :=
  a <- vget (assigns s) (lvar l) ;;
  Ret (if Nat.eqb a 0 then 0
       else if Nat.eqb (Nat.modulo l 2) 0 then a else 3 - a).

Definition decision_level : itree vecE nat := vlen (trail_lim s).

Definition enqueue (l : nat) (r : nat) : itree vecE unit :=
  let v := lvar l in
  vset (assigns s) v (if Nat.eqb (Nat.modulo l 2) 0 then 1 else 2) ;;
  dl <- decision_level ;;
  vset (level s) v dl ;;
  vset (reason s) v r ;;
  vpush (trail s) l.

(** The first [k >= 2] at which [c] has a literal that is not false, + 1. *)
Fixpoint find_watch (fuel : nat) (c : vec nat) (k len : nat) : itree vecE nat :=
  match fuel with
  | O => vabort 1
  | S f =>
    if Nat.leb len k then Ret 0
    else
      l <- vget c k ;;
      v <- lit_value l ;;
      if Nat.eqb v 2 then find_watch f c (k + 1) len else Ret (k + 1)
  end.

(** Slide [ws[i..n)] down to [ws[j..)] and cut the list there. *)
Fixpoint copy_rest (fuel : nat) (ws : vec nat) (i j n : nat) : itree vecE unit :=
  match fuel with
  | O => vabort 2
  | S f =>
    if Nat.leb n i then vshrink ws j
    else x <- vget ws i ;; vset ws j x ;; copy_rest f ws (i + 1) (j + 1) n
  end.

(** Visit the clauses watching [fl], which has just become false.  Each
    either finds another literal to watch, is satisfied, becomes unit, or
    is the conflict -- whose index + 1 is returned (0 for none). *)
Fixpoint prop_watch (fuel : nat) (fl : nat) (ws : vec nat) (i j n : nat)
  : itree vecE nat :=
  match fuel with
  | O => vabort 3
  | S f =>
    if Nat.leb n i then vshrink ws j ;; Ret 0
    else
      ci <- vget ws i ;;
      c <- vget (clauses s) ci ;;
      c0 <- vget c 0 ;;
      (if Nat.eqb c0 fl
       then c1 <- vget c 1 ;; vset c 0 c1 ;; vset c 1 fl
       else Ret tt) ;;
      first <- vget c 0 ;;
      fv <- lit_value first ;;
      if Nat.eqb fv 1 then
        vset ws j ci ;; prop_watch f fl ws (i + 1) (j + 1) n
      else
        len <- vlen c ;;
        k1 <- find_watch fuel c 2 len ;;
        if Nat.eqb k1 0 then
          vset ws j ci ;;
          if Nat.eqb fv 2 then
            copy_rest fuel ws (i + 1) (j + 1) n ;; Ret (ci + 1)
          else
            enqueue first (ci + 1) ;; prop_watch f fl ws (i + 1) (j + 1) n
        else
          let k := k1 - 1 in
          ck <- vget c k ;;
          vset c 1 ck ;;
          vset c k fl ;;
          w <- vget (watches s) ck ;;
          vpush w ci ;;
          prop_watch f fl ws (i + 1) j n
  end.

(** Unit propagation to a fixpoint; the conflict clause's index + 1, or 0. *)
Fixpoint propagate (fuel : nat) : itree vecE nat :=
  match fuel with
  | O => vabort 4
  | S f =>
    qh <- vget (misc s) QHEAD ;;
    tl <- vlen (trail s) ;;
    if Nat.leb tl qh then Ret 0
    else
      p <- vget (trail s) qh ;;
      vset (misc s) QHEAD (qh + 1) ;;
      let fl := lneg p in
      ws <- vget (watches s) fl ;;
      n <- vlen ws ;;
      confl <- prop_watch fuel fl ws 0 0 n ;;
      if Nat.eqb confl 0 then propagate f else Ret confl
  end.

(** Undo the trail from [lim] up, saving each variable's phase. *)
Fixpoint unassign (fuel : nat) (i lim : nat) : itree vecE unit :=
  match fuel with
  | O => vabort 5
  | S f =>
    if Nat.leb i lim then Ret tt
    else
      l <- vget (trail s) (i - 1) ;;
      let v := lvar l in
      a <- vget (assigns s) v ;;
      vset (phase s) v a ;;
      vset (assigns s) v 0 ;;
      vset (reason s) v 0 ;;
      unassign f (i - 1) lim
  end.

Definition backtrack (fuel lvl : nat) : itree vecE unit :=
  dl <- decision_level ;;
  if Nat.leb dl lvl then Ret tt
  else
    lim <- vget (trail_lim s) lvl ;;
    tl <- vlen (trail s) ;;
    unassign fuel tl lim ;;
    vshrink (trail s) lim ;;
    vshrink (trail_lim s) lvl ;;
    vset (misc s) QHEAD lim.

(** Mark the literals of [c] from [j] on; those at the current level count
    towards [pathC], the rest go into [learnt].  The new [pathC]. *)
Fixpoint analyze_lits (fuel : nat) (c : vec nat) (j len dl pathC : nat)
    (learnt : vec nat) (now : nat) : itree vecE nat :=
  match fuel with
  | O => vabort 6
  | S f =>
    if Nat.leb len j then Ret pathC
    else
      q <- vget c j ;;
      let v := lvar q in
      sv <- vget (seen s) v ;;
      lv <- vget (level s) v ;;
      if Nat.eqb sv 0 && Nat.ltb 0 lv then
        vset (seen s) v 1 ;;
        vset (stamp s) v now ;;
        if Nat.leb dl lv then analyze_lits f c (j + 1) len dl (pathC + 1) learnt now
        else vpush learnt q ;; analyze_lits f c (j + 1) len dl pathC learnt now
      else analyze_lits f c (j + 1) len dl pathC learnt now
  end.

(** The highest trail position at or below [i] whose variable is marked. *)
Fixpoint next_seen (fuel : nat) (i : nat) : itree vecE nat :=
  match fuel with
  | O => vabort 7
  | S f =>
    l <- vget (trail s) i ;;
    sv <- vget (seen s) (lvar l) ;;
    if Nat.eqb sv 0 then next_seen f (i - 1) else Ret i
  end.

(** Walk the implication graph back from [confl] to the first UIP, which
    is returned; the other literals of the learnt clause are in [learnt]. *)
Fixpoint analyze_loop (fuel : nat) (confl : nat) (start : nat) (index : nat)
    (pathC dl : nat) (learnt : vec nat) (now : nat) : itree vecE nat :=
  match fuel with
  | O => vabort 8
  | S f =>
    c <- vget (clauses s) confl ;;
    len <- vlen c ;;
    pathC' <- analyze_lits fuel c start len dl pathC learnt now ;;
    idx <- next_seen fuel index ;;
    p <- vget (trail s) idx ;;
    let v := lvar p in
    r <- vget (reason s) v ;;
    vset (seen s) v 0 ;;
    if Nat.leb pathC' 1 then Ret p
    else analyze_loop f (r - 1) 1 (idx - 1) (pathC' - 1) dl learnt now
  end.

(** Clear the marks of [learnt[1..]] and find the deepest level among them,
    moving the literal at that level to position 1.  That level. *)
Fixpoint finish_learnt (fuel : nat) (learnt : vec nat) (i len best bestlv : nat)
  : itree vecE nat :=
  match fuel with
  | O => vabort 9
  | S f =>
    if Nat.leb len i then
      (if Nat.ltb 1 best then
         b <- vget learnt best ;; x <- vget learnt 1 ;;
         vset learnt 1 b ;; vset learnt best x
       else Ret tt) ;;
      Ret bestlv
    else
      q <- vget learnt i ;;
      let v := lvar q in
      vset (seen s) v 0 ;;
      lv <- vget (level s) v ;;
      if Nat.ltb bestlv lv then finish_learnt f learnt (i + 1) len i lv
      else finish_learnt f learnt (i + 1) len best bestlv
  end.

Definition attach (ci : nat) (c : vec nat) : itree vecE unit :=
  c0 <- vget c 0 ;; c1 <- vget c 1 ;;
  w0 <- vget (watches s) c0 ;; vpush w0 ci ;;
  w1 <- vget (watches s) c1 ;; vpush w1 ci.

(** Learn from conflict [confl] (an index) and backjump. *)
Definition learn (fuel confl : nat) : itree vecE unit :=
  dl <- decision_level ;;
  now <- vget (misc s) CONFLICTS ;;
  learnt <- vmake 1 0 ;;
  tl <- vlen (trail s) ;;
  p <- analyze_loop fuel confl 0 (tl - 1) 0 dl learnt now ;;
  let uip := lneg p in
  vset learnt 0 uip ;;
  len <- vlen learnt ;;
  bt <- finish_learnt fuel learnt 1 len 0 0 ;;
  backtrack fuel bt ;;
  if Nat.eqb len 1 then enqueue uip 0
  else
    ci <- vlen (clauses s) ;;
    vpush (clauses s) learnt ;;
    attach ci learnt ;;
    enqueue uip (ci + 1).

(** The unassigned variable most recently seen in a conflict, + 1; 0 when
    every variable is assigned. *)
Fixpoint pick (fuel : nat) (v n best beststamp : nat) : itree vecE nat :=
  match fuel with
  | O => vabort 10
  | S f =>
    if Nat.leb n v then Ret best
    else
      a <- vget (assigns s) v ;;
      if Nat.eqb a 0 then
        st <- vget (stamp s) v ;;
        if Nat.eqb best 0 || Nat.ltb beststamp st
        then pick f (v + 1) n (v + 1) st
        else pick f (v + 1) n best beststamp
      else pick f (v + 1) n best beststamp
  end.

(** 1: satisfiable, 0: unsatisfiable, 2: out of fuel. *)
Fixpoint search (fuel : nat) (budget nvars : nat) : itree vecE nat :=
  match budget with
  | O => Ret 2
  | S b =>
    confl <- propagate fuel ;;
    if Nat.eqb confl 0 then
      v1 <- pick fuel 0 nvars 0 0 ;;
      if Nat.eqb v1 0 then Ret 1
      else
        let v := v1 - 1 in
        ph <- vget (phase s) v ;;
        tl <- vlen (trail s) ;;
        vpush (trail_lim s) tl ;;
        enqueue (lit_of v ph) 0 ;;
        search fuel b nvars
    else
      dl <- decision_level ;;
      if Nat.eqb dl 0 then Ret 0
      else
        k <- vget (misc s) CONFLICTS ;;
        vset (misc s) CONFLICTS (k + 1) ;;
        learn fuel (confl - 1) ;;
        rc <- vget (misc s) RCOUNT ;;
        rl <- vget (misc s) RLIMIT ;;
        (if Nat.leb rl (rc + 1)
         then vset (misc s) RCOUNT 0 ;;
              vset (misc s) RLIMIT (rl + Nat.div rl 2) ;;
              backtrack fuel 0
         else vset (misc s) RCOUNT (rc + 1)) ;;
        search fuel b nvars
  end.

(** Whether one of the [len] literals of [input] from [pos] on is true. *)
Fixpoint clause_sat (fuel : nat) (input : vec nat) (pos len : nat) : itree vecE bool :=
  match fuel with
  | O => vabort 11
  | S f =>
    match len with
    | O => Ret false
    | S len' =>
      l <- vget input pos ;;
      v <- lit_value l ;;
      if Nat.eqb v 1 then Ret true else clause_sat f input (pos + 1) len'
    end
  end.

(** Whether the assignment satisfies the clauses of [input] from [pos] up
    to [n].  It reads the caller's clauses rather than the database, whose
    clauses propagation has reordered in place, so that trusting a model
    needs nothing from the search beyond its leaving [input] alone. *)
Fixpoint check_model (fuel : nat) (input : vec nat) (pos n : nat) : itree vecE bool :=
  match fuel with
  | O => vabort 12
  | S f =>
    if Nat.leb n pos then Ret true
    else
      len <- vget input pos ;;
      ok <- clause_sat fuel input (pos + 1) len ;;
      if ok then check_model f input (pos + 1 + len) n else Ret false
  end.

(** Copy [len] literals of [input] from [pos] into a fresh clause. *)
Fixpoint read_lits (fuel : nat) (input : vec nat) (c : vec nat) (pos len : nat)
  : itree vecE unit :=
  match fuel with
  | O => vabort 13
  | S f =>
    match len with
    | O => Ret tt
    | S len' => l <- vget input pos ;; vpush c l ;; read_lits f input c (pos + 1) len'
    end
  end.

(** Load the clauses of [input] -- each its length, then its literals.
    A unit clause is enqueued at level 0; false when the input is
    already contradictory. *)
Fixpoint load (fuel : nat) (input : vec nat) (pos n : nat) : itree vecE bool :=
  match fuel with
  | O => vabort 14
  | S f =>
    if Nat.leb n pos then Ret true
    else
      len <- vget input pos ;;
      c <- vmake 0 0 ;;
      read_lits fuel input c (pos + 1) len ;;
      ci <- vlen (clauses s) ;;
      vpush (clauses s) c ;;
      if Nat.eqb len 0 then Ret false
      else if Nat.eqb len 1 then
        l <- vget c 0 ;;
        v <- lit_value l ;;
        if Nat.eqb v 2 then Ret false
        else (if Nat.eqb v 0 then enqueue l 0 else Ret tt) ;;
             load f input (pos + 1 + len) n
      else attach ci c ;; load f input (pos + 1 + len) n
  end.

End Ops.

(** [n] distinct empty vectors, pushed onto [acc]. *)
Fixpoint fresh_vecs (fuel : nat) (acc : vec (vec nat)) (n : nat) : itree vecE unit :=
  match fuel with
  | O => vabort 15
  | S f =>
    match n with
    | O => Ret tt
    | S n' => w <- vmake 0 0 ;; vpush acc w ;; fresh_vecs f acc n'
    end
  end.

(** Solve the [ninput]-long clause list [input] over [nvars] variables,
    taking at most [budget] propagate-decide-or-learn steps.  Result:
    [code + 4 * conflicts], where [code] is 1 for a model the solver has
    checked against every clause of [input], 3 for a model that failed that
    check, 0 for unsatisfiable and 2 for out of budget. *)
Definition solve (fuel budget nvars : nat) (input : vec nat) (ninput : nat)
  : itree vecE nat :=
  e <- vmake 0 0 ;;
  cs <- vmake 0 e ;;
  ws <- vmake 0 e ;;
  fresh_vecs fuel ws (2 * nvars) ;;
  asg <- vmake nvars 0 ;;
  lvl <- vmake nvars 0 ;;
  rsn <- vmake nvars 0 ;;
  ph <- vmake nvars 2 ;;
  st <- vmake nvars 0 ;;
  sn <- vmake nvars 0 ;;
  tr <- vmake 0 0 ;;
  tlim <- vmake 0 0 ;;
  m <- vmake 4 0 ;;
  vset m RLIMIT 100 ;;
  let s := mk_state cs ws asg lvl rsn ph st sn tr tlim m in
  ok <- load s fuel input 0 ninput ;;
  code <-
    (if ok then
       r <- search s fuel budget nvars ;;
       if Nat.eqb r 1 then
         good <- check_model s fuel input 0 ninput ;;
         Ret (if good then 1 else 3)
       else Ret r
     else Ret 0) ;;
  k <- vget m CONFLICTS ;;
  Ret (code + 4 * k).

End Solver.
