(** The CDCL solver of [Solver.v], on [Global] arrays instead of [vecE].

    The algorithm, the order of every decision and so the answers and
    conflict counts are those of [Solver.solve_dimacs]; only the storage
    differs.  [Global] arrays have a fixed size and no length, so:
    - lengths live in [misc] cells (trail, trail limits, learnt clause,
      clause arena) or in [wlen] (watch lists);
    - the trail, the trail limits and the learnt-clause scratch hold at most
      [nvars] (+ 1) literals, so they are allocated at that size up front;
    - the clause database is one [nat] arena of [[len; lits...]] records,
      held in a reference and reallocated at twice the size when a clause
      does not fit; a clause is its offset in the arena;
    - each literal's watch list is an array with a capacity in [wcap],
      replaced by one twice as large (+ 4) when it is full.
    Running out of fuel is [failwith] rather than [VAbort]: the C++ throws,
    and the driver reports UNKNOWN.  Nothing here is proved; the theorems of
    [SolverMain.v] are about [Solver]. *)
From Stdlib Require Import PeanoNat Bool List PrimString.
Import ListNotations.
Local Open Scope bool_scope.
From ITree Require Import ITree Events.Exception.
From Crane Require Monads.Global.
From Crane Require Import Monads.ITree Monads.Error Monads.Indices.
Require Solver.

Module SolverGlobal.

(** Index-typed cells holding [nat]s.  [Vn] and [Va] are notations so that
    [Vn 0] and [Va 0] reduce to their element types where Crane reads them;
    as definitions their cells would be type-erased. *)
Notation Vn := (fun _ : nat => nat).
(** A fixed-size array of [nat]s. *)
Definition narr : Type := Global.array nat (Vn 0).
(** Index-typed cells holding [nat] arrays: the arena reference and the
    array of watch lists. *)
Notation Va := (fun _ : nat => narr).

(** The solver's effects: [nat] state, array-of-array state, and failure. *)
Notation E := (Global.Event nat Vn +' Global.Event nat Va +' exceptE Err).

(** Give up: a loop ran out of fuel.  No answer comes back. *)
Definition out_of_fuel {A} (site : string) : itree E A := failwith site.

(** The variable of a literal. *)
Definition lvar (l : nat) : nat := Nat.div l 2.
(** The opposite literal: flip the low bit. *)
Definition lneg (l : nat) : nat :=
  if Nat.eqb (Nat.modulo l 2) 0 then l + 1 else l - 1.
(** The literal of [v] that a value of [a] (1 or 2) makes true. *)
Definition lit_of (v a : nat) : nat := if Nat.eqb a 1 then 2 * v else 2 * v + 1.

(** The solver state: handles to every array, created once by [run]. *)
Record state := mk_state {
  arena : Global.ref (Va 0);       (** the clause arena: [[len; lits...]] per clause *)
  wdata : Global.array nat (Va 0); (** per literal: its watch list's storage *)
  wlen : narr;                     (** per literal: its watch list's length *)
  wcap : narr;                     (** per literal: its watch list's capacity *)
  assigns : narr;                  (** per variable: 0, 1 or 2 *)
  level : narr;                    (** per variable: decision level of its assignment *)
  reason : narr;                   (** per variable: clause offset + 1, or 0 for none *)
  phase : narr;                    (** per variable: the value it last had *)
  stamp : narr;                    (** per variable: conflict count when last bumped *)
  seen : narr;                     (** per variable: scratch for [analyze] *)
  trail : narr;                    (** assigned literals, in order; capacity [nvars] *)
  trail_lim : narr;                (** per decision level: trail length at its decision *)
  learnt : narr;                   (** the clause being learnt; capacity [nvars + 1] *)
  misc : narr                      (** the counters below *)
}.

(** The propagation queue head: a trail position. *)
Definition QHEAD := 0.
(** Conflicts so far. *)
Definition CONFLICTS := 1.
(** Conflicts allowed before the next restart. *)
Definition RLIMIT := 2.
(** Conflicts since the last restart. *)
Definition RCOUNT := 3.
(** The trail's length. *)
Definition TLEN := 4.
(** The number of decision levels. *)
Definition TLLEN := 5.
(** The used length of the clause arena. *)
Definition ALEN := 6.
(** The size of the clause arena's storage. *)
Definition ACAP := 7.
(** The learnt clause's length. *)
Definition LLEN := 8.
(** The number of [misc] cells. *)
Definition NMISC := 9.

(** Copy [n] elements of [src] from [i] on to [dst] from [i] on. *)
Fixpoint copy (fuel : nat) (src dst : narr) (i n : nat) : itree E unit :=
  match fuel with
  | O => out_of_fuel "copy"
  | S f =>
    if Nat.leb n i then Ret tt
    else x <- Global.read_array src i ;; Global.write_array dst i x ;;
         copy f src dst (i + 1) n
  end.

Section Ops.
Variable s : state.

(** Read misc cell [k]. *)
Definition get (k : nat) : itree E nat := Global.read_array (misc s) k.
(** Write misc cell [k]. *)
Definition put (k x : nat) : itree E unit := Global.write_array (misc s) k x.

(** The value of a literal: 0 unassigned, 1 true, 2 false. *)
Definition lit_value (l : nat) : itree E nat :=
  a <- Global.read_array (assigns s) (lvar l) ;;
  Ret (if Nat.eqb a 0 then 0
       else if Nat.eqb (Nat.modulo l 2) 0 then a else 3 - a).

(** The current decision level: the number of trail limits. *)
Definition decision_level : itree E nat := get TLLEN.

(** Make [l] true with reason [r] (clause offset + 1, 0 for a decision),
    at the current level, and push it on the trail. *)
Definition enqueue (l : nat) (r : nat) : itree E unit :=
  let v := lvar l in
  Global.write_array (assigns s) v (if Nat.eqb (Nat.modulo l 2) 0 then 1 else 2) ;;
  dl <- decision_level ;;
  Global.write_array (level s) v dl ;;
  Global.write_array (reason s) v r ;;
  tl <- get TLEN ;;
  Global.write_array (trail s) tl l ;;
  put TLEN (tl + 1).

(** Append clause offset [ci] to the watch list of literal [l], moving the
    list to storage twice as large (+ 4) when it is full. *)
Definition watch (fuel l ci : nat) : itree E unit :=
  n <- Global.read_array (wlen s) l ;;
  cap <- Global.read_array (wcap s) l ;;
  w <- Global.read_array (wdata s) l ;;
  (if Nat.ltb n cap then Global.write_array w n ci
   else
     let cap' := 2 * cap + 4 in
     w' <- Global.new_array 0 cap' 0 ;;
     copy fuel w w' 0 n ;;
     Global.write_array w' n ci ;;
     Global.write_array (wdata s) l w' ;;
     Global.write_array (wcap s) l cap') ;;
  Global.write_array (wlen s) l (n + 1).

(** The first [k >= 2] at which the clause at [co] in arena [a] has a
    literal that is not false, + 1. *)
Fixpoint find_watch (fuel : nat) (a : narr) (co k len : nat) : itree E nat :=
  match fuel with
  | O => out_of_fuel "find_watch"
  | S f =>
    if Nat.leb len k then Ret 0
    else
      l <- Global.read_array a (co + 1 + k) ;;
      v <- lit_value l ;;
      if Nat.eqb v 2 then find_watch f a co (k + 1) len else Ret (k + 1)
  end.

(** Slide [ws[i..n)] down to [ws[j..)] and cut [fl]'s list there. *)
Fixpoint copy_rest (fuel : nat) (fl : nat) (ws : narr) (i j n : nat) : itree E unit :=
  match fuel with
  | O => out_of_fuel "copy_rest"
  | S f =>
    if Nat.leb n i then Global.write_array (wlen s) fl j
    else x <- Global.read_array ws i ;; Global.write_array ws j x ;;
         copy_rest f fl ws (i + 1) (j + 1) n
  end.

(** Visit the clauses watching [fl], which has just become false.  Each
    either finds another literal to watch, is satisfied, becomes unit, or
    is the conflict, whose offset + 1 is returned (0 for none).  No clause
    is added meanwhile, so the arena [a] stays current. *)
Fixpoint prop_watch (fuel : nat) (a : narr) (fl : nat) (ws : narr) (i j n : nat)
  : itree E nat :=
  match fuel with
  | O => out_of_fuel "prop_watch"
  | S f =>
    if Nat.leb n i then Global.write_array (wlen s) fl j ;; Ret 0
    else
      ci <- Global.read_array ws i ;;
      c0 <- Global.read_array a (ci + 1) ;;
      (if Nat.eqb c0 fl
       then c1 <- Global.read_array a (ci + 2) ;;
            Global.write_array a (ci + 1) c1 ;; Global.write_array a (ci + 2) fl
       else Ret tt) ;;
      first <- Global.read_array a (ci + 1) ;;
      fv <- lit_value first ;;
      if Nat.eqb fv 1 then
        Global.write_array ws j ci ;; prop_watch f a fl ws (i + 1) (j + 1) n
      else
        len <- Global.read_array a ci ;;
        k1 <- find_watch fuel a ci 2 len ;;
        if Nat.eqb k1 0 then
          Global.write_array ws j ci ;;
          if Nat.eqb fv 2 then
            copy_rest fuel fl ws (i + 1) (j + 1) n ;; Ret (ci + 1)
          else
            enqueue first (ci + 1) ;; prop_watch f a fl ws (i + 1) (j + 1) n
        else
          let k := k1 - 1 in
          ck <- Global.read_array a (ci + 1 + k) ;;
          Global.write_array a (ci + 2) ck ;;
          Global.write_array a (ci + 1 + k) fl ;;
          watch fuel ck ci ;;
          prop_watch f a fl ws (i + 1) j n
  end.

(** Unit propagation to a fixpoint; the conflict clause's offset + 1, or 0. *)
Fixpoint propagate (fuel : nat) : itree E nat :=
  match fuel with
  | O => out_of_fuel "propagate"
  | S f =>
    qh <- get QHEAD ;;
    tl <- get TLEN ;;
    if Nat.leb tl qh then Ret 0
    else
      p <- Global.read_array (trail s) qh ;;
      put QHEAD (qh + 1) ;;
      let fl := lneg p in
      ws <- Global.read_array (wdata s) fl ;;
      n <- Global.read_array (wlen s) fl ;;
      a <- Global.read_ref (arena s) ;;
      confl <- prop_watch fuel a fl ws 0 0 n ;;
      if Nat.eqb confl 0 then propagate f else Ret confl
  end.

(** Undo the trail from [lim] up, saving each variable's phase. *)
Fixpoint unassign (fuel : nat) (i lim : nat) : itree E unit :=
  match fuel with
  | O => out_of_fuel "unassign"
  | S f =>
    if Nat.leb i lim then Ret tt
    else
      l <- Global.read_array (trail s) (i - 1) ;;
      let v := lvar l in
      a <- Global.read_array (assigns s) v ;;
      Global.write_array (phase s) v a ;;
      Global.write_array (assigns s) v 0 ;;
      Global.write_array (reason s) v 0 ;;
      unassign f (i - 1) lim
  end.

(** Backjump to decision level [lvl]. *)
Definition backtrack (fuel lvl : nat) : itree E unit :=
  dl <- decision_level ;;
  if Nat.leb dl lvl then Ret tt
  else
    lim <- Global.read_array (trail_lim s) lvl ;;
    tl <- get TLEN ;;
    unassign fuel tl lim ;;
    put TLEN lim ;;
    put TLLEN lvl ;;
    put QHEAD lim.

(** Append [q] to the learnt clause.  Each variable goes in once, so it
    never holds more than [nvars + 1] literals. *)
Definition push_learnt (q : nat) : itree E unit :=
  n <- get LLEN ;; Global.write_array (learnt s) n q ;; put LLEN (n + 1).

(** Mark the literals of the clause at [co] from [j] on; those at the
    current level count towards [pathC], the rest go into [learnt].  The
    new [pathC]. *)
Fixpoint analyze_lits (fuel : nat) (a : narr) (co j len dl pathC now : nat)
  : itree E nat :=
  match fuel with
  | O => out_of_fuel "analyze_lits"
  | S f =>
    if Nat.leb len j then Ret pathC
    else
      q <- Global.read_array a (co + 1 + j) ;;
      let v := lvar q in
      sv <- Global.read_array (seen s) v ;;
      lv <- Global.read_array (level s) v ;;
      if Nat.eqb sv 0 && Nat.ltb 0 lv then
        Global.write_array (seen s) v 1 ;;
        Global.write_array (stamp s) v now ;;
        if Nat.leb dl lv then analyze_lits f a co (j + 1) len dl (pathC + 1) now
        else push_learnt q ;; analyze_lits f a co (j + 1) len dl pathC now
      else analyze_lits f a co (j + 1) len dl pathC now
  end.

(** The highest trail position at or below [i] whose variable is marked. *)
Fixpoint next_seen (fuel : nat) (i : nat) : itree E nat :=
  match fuel with
  | O => out_of_fuel "next_seen"
  | S f =>
    l <- Global.read_array (trail s) i ;;
    sv <- Global.read_array (seen s) (lvar l) ;;
    if Nat.eqb sv 0 then next_seen f (i - 1) else Ret i
  end.

(** Walk the implication graph back from the clause at [confl] to the first
    UIP, which is returned; the other literals of the learnt clause are in
    [learnt]. *)
Fixpoint analyze_loop (fuel : nat) (a : narr) (confl start index pathC dl now : nat)
  : itree E nat :=
  match fuel with
  | O => out_of_fuel "analyze_loop"
  | S f =>
    len <- Global.read_array a confl ;;
    pathC' <- analyze_lits fuel a confl start len dl pathC now ;;
    idx <- next_seen fuel index ;;
    p <- Global.read_array (trail s) idx ;;
    let v := lvar p in
    r <- Global.read_array (reason s) v ;;
    Global.write_array (seen s) v 0 ;;
    if Nat.leb pathC' 1 then Ret p
    else analyze_loop f a (r - 1) 1 (idx - 1) (pathC' - 1) dl now
  end.

(** Clear the marks of [learnt[i..len)] and find the deepest level among
    them, moving the literal at that level to position 1.  That level. *)
Fixpoint finish_learnt (fuel : nat) (i len best bestlv : nat) : itree E nat :=
  match fuel with
  | O => out_of_fuel "finish_learnt"
  | S f =>
    if Nat.leb len i then
      (if Nat.ltb 1 best then
         Global.swap_array (learnt s) 1 best
       else Ret tt) ;;
      Ret bestlv
    else
      q <- Global.read_array (learnt s) i ;;
      let v := lvar q in
      Global.write_array (seen s) v 0 ;;
      lv <- Global.read_array (level s) v ;;
      if Nat.ltb bestlv lv then finish_learnt f (i + 1) len i lv
      else finish_learnt f (i + 1) len best bestlv
  end.

(** Room for [need] more cells in the arena: when they do not fit, move it
    to storage of twice the size, or just enough if that is more.  The
    arena, and the offset the next clause goes at. *)
Definition reserve (fuel need : nat) : itree E (narr * nat) :=
  a <- Global.read_ref (arena s) ;;
  n <- get ALEN ;;
  cap <- get ACAP ;;
  if Nat.leb (n + need) cap then Ret (a, n)
  else
    let cap' := Nat.max (2 * cap) (n + need) in
    a' <- Global.new_array 0 cap' 0 ;;
    copy fuel a a' 0 n ;;
    Global.write_ref (arena s) a' ;;
    put ACAP cap' ;;
    Ret (a', n).

(** Watch the first two literals of the clause at [co]. *)
Definition attach (fuel : nat) (a : narr) (co : nat) : itree E unit :=
  c0 <- Global.read_array a (co + 1) ;; c1 <- Global.read_array a (co + 2) ;;
  watch fuel c0 co ;; watch fuel c1 co.

(** Copy [learnt[i..len)] into the arena at [co + 1 + i] on. *)
Fixpoint store_learnt (fuel : nat) (a : narr) (co i len : nat) : itree E unit :=
  match fuel with
  | O => out_of_fuel "store_learnt"
  | S f =>
    if Nat.leb len i then Ret tt
    else q <- Global.read_array (learnt s) i ;;
         Global.write_array a (co + 1 + i) q ;;
         store_learnt f a co (i + 1) len
  end.

(** Learn from the conflict clause at [confl] and backjump. *)
Definition learn (fuel confl : nat) : itree E unit :=
  dl <- decision_level ;;
  now <- get CONFLICTS ;;
  put LLEN 1 ;;
  tl <- get TLEN ;;
  a <- Global.read_ref (arena s) ;;
  p <- analyze_loop fuel a confl 0 (tl - 1) 0 dl now ;;
  let uip := lneg p in
  Global.write_array (learnt s) 0 uip ;;
  len <- get LLEN ;;
  bt <- finish_learnt fuel 1 len 0 0 ;;
  backtrack fuel bt ;;
  if Nat.eqb len 1 then enqueue uip 0
  else
    '(a', co) <- reserve fuel (1 + len) ;;
    Global.write_array a' co len ;;
    store_learnt fuel a' co 0 len ;;
    put ALEN (co + 1 + len) ;;
    attach fuel a' co ;;
    enqueue uip (co + 1).

(** The unassigned variable most recently seen in a conflict, + 1; 0 when
    every variable is assigned. *)
Fixpoint pick (fuel : nat) (v n best beststamp : nat) : itree E nat :=
  match fuel with
  | O => out_of_fuel "pick"
  | S f =>
    if Nat.leb n v then Ret best
    else
      a <- Global.read_array (assigns s) v ;;
      if Nat.eqb a 0 then
        st <- Global.read_array (stamp s) v ;;
        if Nat.eqb best 0 || Nat.ltb beststamp st
        then pick f (v + 1) n (v + 1) st
        else pick f (v + 1) n best beststamp
      else pick f (v + 1) n best beststamp
  end.

(** 1: satisfiable, 0: unsatisfiable, 2: out of budget. *)
Fixpoint search (fuel : nat) (budget nvars : nat) : itree E nat :=
  match budget with
  | O => Ret 2
  | S b =>
    confl <- propagate fuel ;;
    if Nat.eqb confl 0 then
      v1 <- pick fuel 0 nvars 0 0 ;;
      if Nat.eqb v1 0 then Ret 1
      else
        let v := v1 - 1 in
        ph <- Global.read_array (phase s) v ;;
        tl <- get TLEN ;;
        dl <- get TLLEN ;;
        Global.write_array (trail_lim s) dl tl ;;
        put TLLEN (dl + 1) ;;
        enqueue (lit_of v ph) 0 ;;
        search fuel b nvars
    else
      dl <- decision_level ;;
      if Nat.eqb dl 0 then Ret 0
      else
        k <- get CONFLICTS ;;
        put CONFLICTS (k + 1) ;;
        learn fuel (confl - 1) ;;
        rc <- get RCOUNT ;;
        rl <- get RLIMIT ;;
        (if Nat.leb rl (rc + 1)
         then put RCOUNT 0 ;;
              put RLIMIT (rl + Nat.div rl 2) ;;
              backtrack fuel 0
         else put RCOUNT (rc + 1)) ;;
        search fuel b nvars
  end.

(** Whether one of the [len] literals of [input] from [pos] on is true. *)
Fixpoint clause_sat (fuel : nat) (input : narr) (pos len : nat) : itree E bool :=
  match fuel with
  | O => out_of_fuel "clause_sat"
  | S f =>
    match len with
    | O => Ret false
    | S len' =>
      l <- Global.read_array input pos ;;
      v <- lit_value l ;;
      if Nat.eqb v 1 then Ret true else clause_sat f input (pos + 1) len'
    end
  end.

(** Whether the assignment satisfies the clauses of [input] from [pos] up
    to [n]: the caller's clauses, not the arena, whose clauses propagation
    has reordered. *)
Fixpoint check_model (fuel : nat) (input : narr) (pos n : nat) : itree E bool :=
  match fuel with
  | O => out_of_fuel "check_model"
  | S f =>
    if Nat.leb n pos then Ret true
    else
      len <- Global.read_array input pos ;;
      ok <- clause_sat fuel input (pos + 1) len ;;
      if ok then check_model f input (pos + 1 + len) n else Ret false
  end.

(** Load the clauses of [input] -- each its length, then its literals --
    into the arena, which has room for all of them.  A unit clause is
    enqueued at level 0; false when the input is already contradictory. *)
Fixpoint load (fuel : nat) (a input : narr) (pos n : nat) : itree E bool :=
  match fuel with
  | O => out_of_fuel "load"
  | S f =>
    if Nat.leb n pos then Ret true
    else
      len <- Global.read_array input pos ;;
      Global.write_array a pos len ;;
      copy fuel input a (pos + 1) (pos + 1 + len) ;;
      put ALEN (pos + 1 + len) ;;
      if Nat.eqb len 0 then Ret false
      else if Nat.eqb len 1 then
        l <- Global.read_array a (pos + 1) ;;
        v <- lit_value l ;;
        if Nat.eqb v 2 then Ret false
        else (if Nat.eqb v 0 then enqueue l 0 else Ret tt) ;;
             load f a input (pos + 1 + len) n
      else attach fuel a pos ;; load f a input (pos + 1 + len) n
  end.

End Ops.

(** Solve the [ninput]-long clause list [input] over [nvars] variables, as
    [Solver.run]: [code + 8 * conflicts]. *)
Definition run (fuel budget nvars : nat) (input : narr) (ninput : nat)
  : itree E nat :=
  a <- Global.new_array 0 ninput 0 ;;
  ar <- Global.new_ref 0 a ;;
  e <- Global.new_array 0 0 0 ;;
  wd <- Global.new_array 0 (2 * nvars) e ;;
  wl <- Global.new_array 0 (2 * nvars) 0 ;;
  wc <- Global.new_array 0 (2 * nvars) 0 ;;
  asg <- Global.new_array 0 nvars 0 ;;
  lvl <- Global.new_array 0 nvars 0 ;;
  rsn <- Global.new_array 0 nvars 0 ;;
  ph <- Global.new_array 0 nvars 2 ;;
  st <- Global.new_array 0 nvars 0 ;;
  sn <- Global.new_array 0 nvars 0 ;;
  tr <- Global.new_array 0 nvars 0 ;;
  tlim <- Global.new_array 0 nvars 0 ;;
  lr <- Global.new_array 0 (nvars + 1) 0 ;;
  m <- Global.new_array 0 NMISC 0 ;;
  Global.write_array m RLIMIT 100 ;;
  Global.write_array m ACAP ninput ;;
  let s := mk_state ar wd wl wc asg lvl rsn ph st sn tr tlim lr m in
  ok <- load s fuel a input 0 ninput ;;
  code <-
    (if ok then
       r <- search s fuel budget nvars ;;
       if Nat.eqb r 1 then
         good <- check_model s fuel input 0 ninput ;;
         Ret (if good then 1 else 3)
       else Ret r
     else Ret 0) ;;
  k <- Global.read_array m CONFLICTS ;;
  Ret (code + 8 * k).

(** The first [i] elements of [bytes], onto [acc]. *)
Fixpoint read_bytes (bytes : narr) (i : nat) (acc : list nat) : itree E (list nat) :=
  match i with
  | O => Ret acc
  | S i' => b <- Global.read_array bytes i' ;; read_bytes bytes i' (b :: acc)
  end.

(** The length of [F] written as a clause list: each clause its length,
    then its literals. *)
Definition cnf_size (F : list (list nat)) : nat :=
  fold_left (fun n c => n + 1 + Solver.Solver.tlen c 0) F 0.

(** Write [c] into [input] from [pos] on; the position after it. *)
Fixpoint write_lits (input : narr) (c : list nat) (pos : nat) : itree E nat :=
  match c with
  | [] => Ret pos
  | l :: c' => Global.write_array input pos l ;; write_lits input c' (pos + 1)
  end.

(** Write [F] into [input] from [pos] on, each clause as its length and
    then its literals; the position after it. *)
Fixpoint write_cnf (input : narr) (F : list (list nat)) (pos : nat) : itree E nat :=
  match F with
  | [] => Ret pos
  | c :: F' =>
    Global.write_array input pos (Solver.Solver.tlen c 0) ;;
    pos' <- write_lits input c (pos + 1) ;;
    write_cnf input F' pos'
  end.

(** Solve the DIMACS file whose [nbytes] bytes are in [bytes], as
    [Solver.solve_dimacs]: [code + 8 * conflicts], 4 exactly when the bytes
    are not a DIMACS CNF file.  An array has no length, so the caller passes
    it. *)
Definition solve_dimacs (fuel budget : nat) (bytes : narr) (nbytes : nat) : itree E nat :=
  bs <- read_bytes bytes nbytes [] ;;
  match Solver.Solver.parse bs with
  | None => Ret 4
  | Some (nvars, F) =>
    input <- Global.new_array 0 (cnf_size F) 0 ;;
    ninput <- write_cnf input F 0 ;;
    run fuel budget nvars input ninput
  end.

End SolverGlobal.
