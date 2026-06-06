From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Bool.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyConditionalRecursion.

(* cached_sum: walk a list; if cache is populated, use it; else recurse.
   Recursion is conditional — only one branch of the match on cache recurses. *)
Fixpoint cached_sum (cache : option nat) (l : list nat) : nat * nat :=
  match l with
  | [] => (0, 0)
  | x :: rest =>
    let sub := match cache with
               | Some v => (v, 0)
               | None => cached_sum None rest
               end
    in
    (x + fst sub, snd sub + 1)
  end.

(* find_or_recurse: if element matches target, return immediately;
   otherwise recurse to search the rest. One branch of the if recurses. *)
Fixpoint find_or_recurse (target : nat) (l : list nat) : nat * list nat :=
  match l with
  | [] => (0, [])
  | x :: rest =>
    let sub := if x =? target
               then (x, rest)
               else find_or_recurse target rest
    in
    (fst sub + 1, snd sub)
  end.

(* nested_cond: nested conditional where recursion is in only one inner branch *)
Fixpoint nested_cond (threshold lo hi : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: rest =>
    let sub := if lo <=? x
               then if x <=? hi
                    then (x, true)
                    else if x <=? threshold
                         then (nested_cond threshold lo hi rest, false)
                         else (0, true)
               else (0, true)
    in
    fst sub + (if snd sub then 1 else 0)
  end.

(* multi_return: returns a pair; conditional recursion + post-processing
   on both components. Closest to max_pref_fn_M. *)
Fixpoint multi_return (memo : option (nat * nat)) (l : list nat)
  : nat * option (nat * nat) :=
  match l with
  | [] => (0, None)
  | x :: rest =>
    let sub := match memo with
               | Some p => (0, Some p)
               | None => multi_return None rest
               end
    in
    let count := fst sub in
    let payload := snd sub in
    match payload with
    | None => (count + 1, None)
    | Some (a, b) => (count + 1, Some (a + x, b))
    end
  end.

(* accum_with_cache: accumulate over a list with a cache lookup.
   If cache hit, use cached partial result; if miss, recurse.
   Uses a nat key to simulate cache lookup. *)
Fixpoint accum_with_cache (key : nat) (l : list nat) : nat * nat :=
  match l with
  | [] => (0, 0)
  | x :: rest =>
    let cached := if x =? key then Some (x * 2) else None in
    let sub := match cached with
               | Some v => (v, 0)
               | None => accum_with_cache key rest
               end
    in
    (fst sub + x, snd sub + 1)
  end.

End LoopifyConditionalRecursion.

Set Crane Loopify.
Crane Extraction "loopify_conditional_recursion" LoopifyConditionalRecursion.
