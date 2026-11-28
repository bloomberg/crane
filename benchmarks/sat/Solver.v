(** A CDCL SAT solver over [Global] arrays and references
    (theories/Monads/Global.v): two-watched-literal propagation, first-UIP
    learning with non-chronological backjumping, phase saving,
    recency-ordered decisions and geometric restarts.

    Every piece of mutable state is a [Global] array or reference.  Crane
    erases the tree and compiles each access to a direct array access; the
    proofs read the same program through [Global]'s model, where an access
    out of bounds fails.  The entry point is [solve_dimacs], which also
    parses the file.

    Encoding: variable [v] has literals [2v] (positive) and [2v+1]
    (negative).  A variable's value is 0 (unassigned), 1 (true) or
    2 (false); a literal's value is read off the same three. *)
From Stdlib Require Import PeanoNat Bool List PrimString.
Import ListNotations.
Local Open Scope bool_scope.
From ITree Require Import ITree Events.Exception.
From Crane Require Monads.Global.
From Crane Require Import Monads.ITree Monads.Error Monads.Indices.

Module Solver.

(** * Literals *)

(** The variable of a literal. *)
Definition lvar (l : nat) : nat := Nat.div l 2.
(** The opposite literal: flip the low bit. *)
Definition lneg (l : nat) : nat :=
  if Nat.eqb (Nat.modulo l 2) 0 then l + 1 else l - 1.
(** The literal of [v] that a value of [a] (1 or 2) makes true. *)
Definition lit_of (v a : nat) : nat := if Nat.eqb a 1 then 2 * v else 2 * v + 1.

(** * State

    The clause database is one arena of [nat]s holding each clause as a
    record [len; lit_0; ...; lit_(len-1)]; a clause is named by the offset
    of its record.  The arena sits in a reference because it moves to
    larger storage when a learnt clause does not fit.  Each literal's watch
    list is an array of clause offsets with a length in [wlen] and a
    capacity in [wcap]; it too moves when full.  The trail, the trail
    limits and the learnt clause have fixed capacities, since each holds a
    variable at most once.  The scalar counters live in [misc]. *)

(** Cells holding [nat]s.  [Vn] and [Va] are notations, not definitions,
    so that [Vn 0] reduces to [nat] where Crane reads it. *)
Notation Vn := (fun _ : nat => nat).
(** A fixed-size array of [nat]s. *)
Definition narr : Type := Global.array nat (Vn 0).
(** Cells holding [nat] arrays: the arena reference and the watch lists. *)
Notation Va := (fun _ : nat => narr).

(** The solver's effects: [nat] cells, array cells, and failure. *)
Notation E := (Global.Event nat Vn +' Global.Event nat Va +' exceptE Err).

(** Give up: a loop ran out of fuel.  No answer comes back; the driver
    reports UNKNOWN. *)
Definition out_of_fuel : itree E nat := failwith "out of fuel"%pstring.

(** Handles to every array, made once by [new_state]. *)
Record state := mk_state {
  arena : Global.ref (Va 0);       (** the clause arena *)
  wdata : Global.array nat (Va 0); (** per literal: its watch list's storage *)
  wlen : narr;                     (** per literal: its watch list's length *)
  wcap : narr;                     (** per literal: its watch list's capacity *)
  assigns : narr;                  (** per variable: 0, 1 or 2 *)
  level : narr;                    (** per variable: decision level of its assignment *)
  reason : narr;                   (** per variable: clause offset + 1, or 0 for none *)
  phase : narr;                    (** per variable: the value it last had *)
  stamp : narr;                    (** per variable: conflict count when last bumped *)
  seen : narr;                     (** per variable: scratch for conflict analysis *)
  trail : narr;                    (** assigned literals, in order; capacity [nvars] *)
  trail_lim : narr;                (** per decision level: trail length at its decision *)
  learnt : narr;                   (** the clause being learnt; capacity [nvars + 1] *)
  misc : narr                      (** the counters below *)
}.

(** [misc] slot: the propagation queue head, a trail position. *)
Definition QHEAD := 0.
(** [misc] slot: conflicts so far. *)
Definition CONFLICTS := 1.
(** [misc] slot: conflicts allowed before the next restart. *)
Definition RLIMIT := 2.
(** [misc] slot: conflicts since the last restart. *)
Definition RCOUNT := 3.
(** [misc] slot: the trail's length. *)
Definition TLEN := 4.
(** [misc] slot: the number of decision levels. *)
Definition TLLEN := 5.
(** [misc] slot: the used length of the arena. *)
Definition ALEN := 6.
(** [misc] slot: the size of the arena's storage. *)
Definition ACAP := 7.
(** [misc] slot: the learnt clause's length. *)
Definition LLEN := 8.
(** The number of [misc] slots. *)
Definition NMISC := 9.

(** The length of [l], plus [n]; tail-recursive. *)
Fixpoint tlen {A} (l : list A) (n : nat) : nat :=
  match l with [] => n | _ :: l' => tlen l' (S n) end.

(** Copy elements [i .. i + n) of [src] to the same positions of [dst]. *)
Fixpoint copy (src dst : narr) (i n : nat) : itree E unit :=
  match n with
  | O => Ret tt
  | S n' =>
    x <- Global.read_array src i ;;
    Global.write_array dst i x ;;
    copy src dst (i + 1) n'
  end.

Section Ops.
(** Every operation below acts on this one state. *)
Variable s : state.

(** * Counters and assignments *)

(** Read [misc] slot [k]. *)
Definition get (k : nat) : itree E nat := Global.read_array (misc s) k.
(** Write [misc] slot [k]. *)
Definition put (k x : nat) : itree E unit := Global.write_array (misc s) k x.

(** The value of a literal: 0 unassigned, 1 true, 2 false. *)
Definition lit_value (l : nat) : itree E nat :=
  a <- Global.read_array (assigns s) (lvar l) ;;
  Ret (if Nat.eqb a 0 then 0
       else if Nat.eqb (Nat.modulo l 2) 0 then a else 3 - a).

(** The current decision level: the number of trail limits. *)
Definition decision_level : itree E nat := get TLLEN.

(** Make [l] true with reason [r] (clause offset + 1, 0 for none) at the
    current level, and push it on the trail. *)
Definition enqueue (l r : nat) : itree E unit :=
  let v := lvar l in
  Global.write_array (assigns s) v (if Nat.eqb (Nat.modulo l 2) 0 then 1 else 2) ;;
  dl <- decision_level ;;
  Global.write_array (level s) v dl ;;
  Global.write_array (reason s) v r ;;
  tl <- get TLEN ;;
  Global.write_array (trail s) tl l ;;
  put TLEN (tl + 1).

(** * Watch lists *)

(** Append clause [co] to the watch list of [l], moving the list to
    storage twice as large (+ 4) when it is full. *)
Definition watch (l co : nat) : itree E unit :=
  n <- Global.read_array (wlen s) l ;;
  cap <- Global.read_array (wcap s) l ;;
  w <- Global.read_array (wdata s) l ;;
  (if Nat.ltb n cap then Global.write_array w n co
   else
     let cap' := 2 * cap + 4 in
     w' <- Global.new_array 0 cap' 0 ;;
     copy w w' 0 n ;;
     Global.write_array w' n co ;;
     Global.write_array (wdata s) l w' ;;
     Global.write_array (wcap s) l cap') ;;
  Global.write_array (wlen s) l (n + 1).

(** Watch the first two literals of clause [co] of arena [a]. *)
Definition attach (a : narr) (co : nat) : itree E unit :=
  c0 <- Global.read_array a (co + 1) ;;
  c1 <- Global.read_array a (co + 2) ;;
  watch c0 co ;;
  watch c1 co.

(** * Propagation *)

(** Among the [m] literals of clause [co] from position [k] on, the first
    one that is not false: its position + 1, or 0 if there is none. *)
Fixpoint find_watch (a : narr) (co k m : nat) : itree E nat :=
  match m with
  | O => Ret 0
  | S m' =>
    l <- Global.read_array a (co + 1 + k) ;;
    v <- lit_value l ;;
    if Nat.eqb v 2 then find_watch a co (k + 1) m' else Ret (k + 1)
  end.

(** Slide the last [m] entries of [fl]'s watch list [ws], from [i] on,
    down to [j], and cut the list after them. *)
Fixpoint copy_rest (fl : nat) (ws : narr) (i j m : nat) : itree E unit :=
  match m with
  | O => Global.write_array (wlen s) fl j
  | S m' =>
    x <- Global.read_array ws i ;;
    Global.write_array ws j x ;;
    copy_rest fl ws (i + 1) (j + 1) m'
  end.

(** Visit the last [m] clauses of the watch list [ws] of [fl], which has
    just become false, from [i] on; the clauses kept so far fill [ws] up
    to [j].  Each clause finds another literal to watch, is satisfied,
    becomes unit, or is the conflict, whose offset + 1 is returned (0 for
    none).  No clause is added meanwhile, so the arena [a] stays current. *)
Fixpoint prop_watch (a : narr) (fl : nat) (ws : narr) (i j m : nat) : itree E nat :=
  match m with
  | O => Global.write_array (wlen s) fl j ;; Ret 0
  | S m' =>
    co <- Global.read_array ws i ;;
    (* Put [fl] second, so that the first literal is the other watch. *)
    c0 <- Global.read_array a (co + 1) ;;
    (if Nat.eqb c0 fl
     then c1 <- Global.read_array a (co + 2) ;;
          Global.write_array a (co + 1) c1 ;;
          Global.write_array a (co + 2) fl
     else Ret tt) ;;
    first <- Global.read_array a (co + 1) ;;
    fv <- lit_value first ;;
    if Nat.eqb fv 1 then
      Global.write_array ws j co ;;
      prop_watch a fl ws (i + 1) (j + 1) m'
    else
      len <- Global.read_array a co ;;
      k1 <- find_watch a co 2 (len - 2) ;;
      if Nat.eqb k1 0 then
        Global.write_array ws j co ;;
        if Nat.eqb fv 2 then
          copy_rest fl ws (i + 1) (j + 1) m' ;;
          Ret (co + 1)
        else
          enqueue first (co + 1) ;;
          prop_watch a fl ws (i + 1) (j + 1) m'
      else
        let k := k1 - 1 in
        ck <- Global.read_array a (co + 1 + k) ;;
        Global.write_array a (co + 2) ck ;;
        Global.write_array a (co + 1 + k) fl ;;
        watch ck co ;;
        prop_watch a fl ws (i + 1) j m'
  end.

(** Unit propagation to a fixpoint: the conflict clause's offset + 1, or
    0 when there is none. *)
Fixpoint propagate (fuel : nat) : itree E nat :=
  match fuel with
  | O => out_of_fuel
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
      confl <- prop_watch a fl ws 0 0 n ;;
      if Nat.eqb confl 0 then propagate f else Ret confl
  end.

(** * Backjumping *)

(** Undo the [m] trail entries below position [i], saving each
    variable's phase. *)
Fixpoint unassign (i m : nat) : itree E unit :=
  match m with
  | O => Ret tt
  | S m' =>
    l <- Global.read_array (trail s) (i - 1) ;;
    let v := lvar l in
    a <- Global.read_array (assigns s) v ;;
    Global.write_array (phase s) v a ;;
    Global.write_array (assigns s) v 0 ;;
    Global.write_array (reason s) v 0 ;;
    unassign (i - 1) m'
  end.

(** Backjump to decision level [lvl]. *)
Definition backtrack (lvl : nat) : itree E unit :=
  dl <- decision_level ;;
  if Nat.leb dl lvl then Ret tt
  else
    lim <- Global.read_array (trail_lim s) lvl ;;
    tl <- get TLEN ;;
    unassign tl (tl - lim) ;;
    put TLEN lim ;;
    put TLLEN lvl ;;
    put QHEAD lim.

(** * Conflict analysis *)

(** Append [q] to the learnt clause.  Each variable goes in once, so it
    never holds more than [nvars + 1] literals. *)
Definition push_learnt (q : nat) : itree E unit :=
  n <- get LLEN ;;
  Global.write_array (learnt s) n q ;;
  put LLEN (n + 1).

(** Mark the [m] literals of clause [co] from position [j] on, stamping
    them with [now]; those at the current level [dl] count towards
    [pathC], the others go into the learnt clause.  The new [pathC]. *)
Fixpoint analyze_lits (a : narr) (co j m dl pathC now : nat) : itree E nat :=
  match m with
  | O => Ret pathC
  | S m' =>
    q <- Global.read_array a (co + 1 + j) ;;
    let v := lvar q in
    sv <- Global.read_array (seen s) v ;;
    lv <- Global.read_array (level s) v ;;
    if Nat.eqb sv 0 && Nat.ltb 0 lv then
      Global.write_array (seen s) v 1 ;;
      Global.write_array (stamp s) v now ;;
      if Nat.leb dl lv then analyze_lits a co (j + 1) m' dl (pathC + 1) now
      else push_learnt q ;; analyze_lits a co (j + 1) m' dl pathC now
    else analyze_lits a co (j + 1) m' dl pathC now
  end.

(** The highest trail position at or below [i] whose variable is marked. *)
Fixpoint next_seen (fuel i : nat) : itree E nat :=
  match fuel with
  | O => out_of_fuel
  | S f =>
    l <- Global.read_array (trail s) i ;;
    sv <- Global.read_array (seen s) (lvar l) ;;
    if Nat.eqb sv 0 then next_seen f (i - 1) else Ret i
  end.

(** Walk the implication graph back from clause [confl], skipping its
    first [start] literals, to the first UIP, which is returned; the other
    literals of the learnt clause go into [learnt].  The walk goes down
    the trail from [index], with [pathC] marked literals of level [dl]
    still to resolve. *)
Fixpoint analyze_loop (fuel : nat) (a : narr) (confl start index pathC dl now : nat)
  : itree E nat :=
  match fuel with
  | O => out_of_fuel
  | S f =>
    len <- Global.read_array a confl ;;
    pathC' <- analyze_lits a confl start (len - start) dl pathC now ;;
    idx <- next_seen fuel index ;;
    p <- Global.read_array (trail s) idx ;;
    let v := lvar p in
    r <- Global.read_array (reason s) v ;;
    Global.write_array (seen s) v 0 ;;
    if Nat.leb pathC' 1 then Ret p
    else analyze_loop f a (r - 1) 1 (idx - 1) (pathC' - 1) dl now
  end.

(** Clear the marks of the [m] learnt literals from position [i] on and
    find the deepest level among them, [best] being the position of the
    deepest so far and [bestlv] its level.  At the end that literal moves
    to position 1, and its level is returned. *)
Fixpoint finish_learnt (i m best bestlv : nat) : itree E nat :=
  match m with
  | O =>
    (if Nat.ltb 1 best then Global.swap_array (learnt s) 1 best else Ret tt) ;;
    Ret bestlv
  | S m' =>
    q <- Global.read_array (learnt s) i ;;
    let v := lvar q in
    Global.write_array (seen s) v 0 ;;
    lv <- Global.read_array (level s) v ;;
    if Nat.ltb bestlv lv then finish_learnt (i + 1) m' i lv
    else finish_learnt (i + 1) m' best bestlv
  end.

(** * Learning *)

(** Room for [need] more cells in the arena: when they do not fit, move it
    to storage twice as large, or just large enough if that is more.  The
    arena, and the offset the next clause goes at. *)
Definition reserve (need : nat) : itree E (narr * nat) :=
  a <- Global.read_ref (arena s) ;;
  n <- get ALEN ;;
  cap <- get ACAP ;;
  if Nat.leb (n + need) cap then Ret (a, n)
  else
    let cap' := Nat.max (2 * cap) (n + need) in
    a' <- Global.new_array 0 cap' 0 ;;
    copy a a' 0 n ;;
    Global.write_ref (arena s) a' ;;
    put ACAP cap' ;;
    Ret (a', n).

(** Copy the [m] learnt literals from position [i] on into clause [co] of
    arena [a]. *)
Fixpoint store_learnt (a : narr) (co i m : nat) : itree E unit :=
  match m with
  | O => Ret tt
  | S m' =>
    q <- Global.read_array (learnt s) i ;;
    Global.write_array a (co + 1 + i) q ;;
    store_learnt a co (i + 1) m'
  end.

(** Learn a clause from the conflict clause [confl], backjump, and assert
    the clause's first-UIP literal. *)
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
  bt <- finish_learnt 1 (len - 1) 0 0 ;;
  backtrack bt ;;
  if Nat.eqb len 1 then enqueue uip 0
  else
    '(a', co) <- reserve (1 + len) ;;
    Global.write_array a' co len ;;
    store_learnt a' co 0 len ;;
    put ALEN (co + 1 + len) ;;
    attach a' co ;;
    enqueue uip (co + 1).

(** * Search *)

(** Among the [m] variables from [v] on, the unassigned one most recently
    seen in a conflict, + 1, against the best so far: [best] (+ 1, 0 for
    none) with stamp [beststamp]. *)
Fixpoint pick (v m best beststamp : nat) : itree E nat :=
  match m with
  | O => Ret best
  | S m' =>
    a <- Global.read_array (assigns s) v ;;
    if Nat.eqb a 0 then
      st <- Global.read_array (stamp s) v ;;
      if Nat.eqb best 0 || Nat.ltb beststamp st
      then pick (v + 1) m' (v + 1) st
      else pick (v + 1) m' best beststamp
    else pick (v + 1) m' best beststamp
  end.

(** Open a decision level and assign [v] its saved phase. *)
Definition decide (v : nat) : itree E unit :=
  ph <- Global.read_array (phase s) v ;;
  tl <- get TLEN ;;
  dl <- get TLLEN ;;
  Global.write_array (trail_lim s) dl tl ;;
  put TLLEN (dl + 1) ;;
  enqueue (lit_of v ph) 0.

(** Count a conflict towards the restart limit; on reaching it, restart
    and raise the limit by half. *)
Definition restart_tick : itree E unit :=
  rc <- get RCOUNT ;;
  rl <- get RLIMIT ;;
  if Nat.leb rl (rc + 1)
  then put RCOUNT 0 ;;
       put RLIMIT (rl + Nat.div rl 2) ;;
       backtrack 0
  else put RCOUNT (rc + 1).

(** Propagate, then decide or learn, for at most [budget] steps over the
    variables [0 .. nvars): 1 satisfiable, 0 unsatisfiable, 2 out of
    budget. *)
Fixpoint search (fuel budget nvars : nat) : itree E nat :=
  match budget with
  | O => Ret 2
  | S b =>
    confl <- propagate fuel ;;
    if Nat.eqb confl 0 then
      v1 <- pick 0 nvars 0 0 ;;
      if Nat.eqb v1 0 then Ret 1
      else decide (v1 - 1) ;; search fuel b nvars
    else
      dl <- decision_level ;;
      if Nat.eqb dl 0 then Ret 0
      else
        k <- get CONFLICTS ;;
        put CONFLICTS (k + 1) ;;
        learn fuel (confl - 1) ;;
        restart_tick ;;
        search fuel b nvars
  end.

(** * Loading and checking *)

(** Write the literals [c] into arena [a] from [pos] on. *)
Fixpoint store_lits (a : narr) (c : list nat) (pos : nat) : itree E unit :=
  match c with
  | [] => Ret tt
  | l :: c' => Global.write_array a pos l ;; store_lits a c' (pos + 1)
  end.

(** Load the clauses [F] into arena [a] from offset [pos] on, where there
    is room for them: watch the first two literals of each longer clause
    and assert each unit clause at level 0.  False when [F] is already
    contradictory. *)
Fixpoint load (a : narr) (F : list (list nat)) (pos : nat) : itree E bool :=
  match F with
  | [] => Ret true
  | c :: F' =>
    let len := tlen c 0 in
    Global.write_array a pos len ;;
    store_lits a c (pos + 1) ;;
    put ALEN (pos + 1 + len) ;;
    match c with
    | [] => Ret false
    | [l] =>
      v <- lit_value l ;;
      if Nat.eqb v 2 then Ret false
      else (if Nat.eqb v 0 then enqueue l 0 else Ret tt) ;;
           load a F' (pos + 1 + len)
    | _ => attach a pos ;; load a F' (pos + 1 + len)
    end
  end.

(** Whether the assignment makes a literal of [c] true. *)
Fixpoint clause_sat (c : list nat) : itree E bool :=
  match c with
  | [] => Ret false
  | l :: c' => v <- lit_value l ;; if Nat.eqb v 1 then Ret true else clause_sat c'
  end.

(** Whether the assignment satisfies every clause of [F]. *)
Fixpoint check_model (F : list (list nat)) : itree E bool :=
  match F with
  | [] => Ret true
  | c :: F' => ok <- clause_sat c ;; if ok then check_model F' else Ret false
  end.

End Ops.

(** * Running *)

(** A fresh state over [nvars] variables with an arena of size [cap]:
    nothing assigned, every phase false, every watch list empty. *)
Definition new_state (nvars cap : nat) : itree E state :=
  a <- Global.new_array 0 cap 0 ;;
  ar <- Global.new_ref 0 a ;;
  empty <- Global.new_array 0 0 0 ;;
  wd <- Global.new_array 0 (2 * nvars) empty ;;
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
  Global.write_array m ACAP cap ;;
  Ret (mk_state ar wd wl wc asg lvl rsn ph st sn tr tlim lr m).

(** The arena size the clauses [F] take: per clause, its length and then
    its literals. *)
Definition cnf_size (F : list (list nat)) : nat :=
  fold_left (fun n c => n + 1 + tlen c 0) F 0.

(** Solve the clauses [F] over the variables [0 .. nvars):
    [code + 8 * conflicts], where [code] is 1 satisfiable (with the model
    checked against [F]), 3 a model that failed that check, 0
    unsatisfiable, 2 out of budget. *)
Definition run (fuel budget nvars : nat) (F : list (list nat)) : itree E nat :=
  s <- new_state nvars (cnf_size F) ;;
  a <- Global.read_ref (arena s) ;;
  ok <- load s a F 0 ;;
  code <-
    (if ok then
       r <- search s fuel budget nvars ;;
       if Nat.eqb r 1 then
         good <- check_model s F ;;
         Ret (if good then 1 else 3)
       else Ret r
     else Ret 0) ;;
  k <- get s CONFLICTS ;;
  Ret (code + 8 * k).

(** * Parsing DIMACS

    The parser is pure and every list function on its path is
    tail-recursive, so the extracted code needs constant stack whatever
    the input.  [DimacsSpec] proves that it accepts exactly the files of
    [DimacsSpec.dimacs] and returns their formula. *)

(** Whitespace: space (byte 32) and bytes 9 to 13 ([\t] to [\r]). *)
Definition is_space (b : nat) : bool := Nat.eqb b 32 || (Nat.leb 9 b && Nat.leb b 13).
(** An ASCII decimal digit, ['0'] (48) to ['9'] (57). *)
Definition is_digit (b : nat) : bool := Nat.leb 48 b && Nat.leb b 57.

(** [bs] cut at every byte [sep] accepts, the pieces in order: [rev acc]
    then [rev cur ++] the first piece of [bs] and the rest. *)
Fixpoint split_tr (sep : nat -> bool) (bs cur : list nat) (acc : list (list nat))
  : list (list nat) :=
  match bs with
  | [] => rev_append acc [rev_append cur []]
  | b :: bs' =>
    if sep b then split_tr sep bs' [] (rev_append cur [] :: acc)
    else split_tr sep bs' (b :: cur) acc
  end.

(** The lines up to the first one starting with ['%'], without the ones
    starting with ['c']. *)
Fixpoint content_tr (ls acc : list (list nat)) : list (list nat) :=
  match ls with
  | [] => rev_append acc []
  | l :: ls' =>
    match l with
    | b :: _ =>
      if Nat.eqb b 37 then rev_append acc []
      else if Nat.eqb b 99 then content_tr ls' acc
      else content_tr ls' (l :: acc)
    | [] => content_tr ls' (l :: acc)
    end
  end.

(** The non-empty pieces of [ws], reversed onto [acc]. *)
Fixpoint nonempty_tr (ws acc : list (list nat)) : list (list nat) :=
  match ws with
  | [] => acc
  | [] :: ws' => nonempty_tr ws' acc
  | w :: ws' => nonempty_tr ws' (w :: acc)
  end.

(** The words of the content lines, reversed onto [acc]. *)
Fixpoint words_tr (ls acc : list (list nat)) : list (list nat) :=
  match ls with
  | [] => acc
  | l :: ls' => words_tr ls' (nonempty_tr (split_tr is_space l [] []) acc)
  end.

(** The tokens of a file, in order: the words of its content lines.
    [DimacsSpec.tokens_tr_eq] equates it with the declarative [tokens]. *)
Definition tokens_tr (bs : list nat) : list (list nat) :=
  rev_append (words_tr (content_tr (split_tr (Nat.eqb 10) bs [] []) []) []) [].

(** The largest variable a file may mention. *)
Definition MAXVAR : nat := Nat.pow 2 32.

(** The value of the decimal digits [w] after [acc], if it is at most
    [cap].  Accumulation stops once [cap] is passed, so it never grows
    beyond [10 * cap + 9]. *)
Fixpoint sdigits (cap acc : nat) (w : list nat) : option nat :=
  match w with
  | [] => if Nat.leb acc cap then Some acc else None
  | d :: w' =>
    if is_digit d then sdigits cap (if Nat.ltb cap acc then acc else 10 * acc + (d - 48)) w'
    else None
  end.

(** The value of the non-empty digit string [w], if it is at most [cap]. *)
Definition snum (cap : nat) (w : list nat) : option nat :=
  match w with [] => None | _ :: _ => sdigits cap 0 w end.

(** The literal a word spells, given at most [nv] variables: DIMACS [x]
    becomes [2 * (x - 1)], and [-x] becomes [2 * (x - 1) + 1]. *)
Definition slit (nv : nat) (w : list nat) : option nat :=
  let nw := match w with
            | b :: w' => if Nat.eqb b 45 then (1, w') else (0, w)
            | [] => (0, w)
            end in
  match snum nv (snd nw) with
  | Some (S v) => Some (2 * v + fst nw)
  | _ => None
  end.

(** Whether [w] ends a clause: a digit string of value 0. *)
Definition is_zero (w : list nat) : bool :=
  match snum 0 w with Some _ => true | None => false end.

(** The clauses the words [ts] spell, after the reversed clauses [acc] and
    with the reversed literals [cur] of an unfinished clause; also their
    number after [cnt], and the largest variable after [maxv]. *)
Fixpoint pclauses (nv : nat) (ts : list (list nat)) (cur : list nat)
    (acc : list (list nat)) (cnt maxv : nat) : option (list (list nat) * nat * nat) :=
  match ts with
  | [] => match cur with [] => Some (rev_append acc [], cnt, maxv) | _ :: _ => None end
  | t :: ts' =>
    if is_zero t then pclauses nv ts' [] (rev_append cur [] :: acc) (cnt + 1) maxv
    else
      match slit nv t with
      | Some l => pclauses nv ts' (l :: cur) acc cnt (Nat.max maxv (Nat.div l 2 + 1))
      | None => None
      end
  end.

(** The number of variables the formula mentions, and its clauses. *)
Definition parse (bs : list nat) : option (nat * list (list nat)) :=
  match tokens_tr bs with
  | tp :: tc :: tnv :: tnc :: ts =>
    let hdr := match tp, tc with
               | [p], [c; n; f] => Nat.eqb p 112 && Nat.eqb c 99 && Nat.eqb n 110 && Nat.eqb f 102
               | _, _ => false
               end in
    if hdr then
      match snum MAXVAR tnv with
      | Some nv =>
        match pclauses nv ts [] [] 0 0 with
        | Some (F, cnt, maxv) =>
          match snum cnt tnc with
          | Some k => if Nat.eqb k cnt then Some (maxv, F) else None
          | None => None
          end
        | None => None
        end
      | None => None
      end
    else None
  | _ => None
  end.

(** * Entry point *)

(** The first [i] elements of [bytes], onto [acc]. *)
Fixpoint read_bytes (bytes : narr) (i : nat) (acc : list nat) : itree E (list nat) :=
  match i with
  | O => Ret acc
  | S i' => b <- Global.read_array bytes i' ;; read_bytes bytes i' (b :: acc)
  end.

(** Solve the DIMACS file whose [nbytes] bytes are in [bytes]:
    [code + 8 * conflicts] as for [run], or 4 exactly when the bytes are
    not a DIMACS CNF file.  An array has no length, so the caller passes
    it. *)
Definition solve_dimacs (fuel budget : nat) (bytes : narr) (nbytes : nat) : itree E nat :=
  bs <- read_bytes bytes nbytes [] ;;
  match parse bs with
  | None => Ret 4
  | Some (nvars, F) => run fuel budget nvars F
  end.

End Solver.
