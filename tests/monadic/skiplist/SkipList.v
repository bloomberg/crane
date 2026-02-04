(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   STM-based Skip List implementation
   Ported from Haskell's tskiplist package:
   https://hackage.haskell.org/package/tskiplist-1.0.1/docs/Control-Concurrent-STM-SkipList.html

   A skip list is a probabilistic data structure with dictionary operations.
   In contrast to a balanced tree, a skip list does not need any expensive
   rebalancing operation, making it suitable for concurrent programming.

   Reference: William Pugh. Skip Lists: A Probabilistic Alternative to Balanced Trees.

   Implementation note: Since Rocq's positivity checker doesn't allow recursive
   types through TVar, we use an axiomatized Node type that extracts to C++
   shared_ptr-based nodes.
*)

From Stdlib Require Import List Bool Arith Program.Wf.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.STM.
From Corelib Require Import PrimInt63.

Import ListNotations.
Import MonadNotations.
Set Implicit Arguments.

(* ========================================================================= *)
(*                              Configuration                                *)
(* ========================================================================= *)

(* Maximum number of levels - supports up to 2^16 elements efficiently *)
Definition maxLevels : nat := sixteen.

Crane Extract Inlined Constant maxLevels => "16u".

(* ========================================================================= *)
(*                         Random Level Generation                           *)
(* ========================================================================= *)

(* Axiom for random number generation *)
Module Random_axioms.
  Axiom irandomInt : int -> IO_axioms.iIO int.
End Random_axioms.

Crane Extract Skip Module Random_axioms.
Import Random_axioms.

Definition randomInt (bound : int) : IO int := trigger (irandomInt bound).

Crane Extract Inlined Constant randomInt =>
  "(std::rand() % %a0)" From "cstdlib".

(* Choose a random level for a new node *)
Fixpoint chooseLevel_aux (fuel : nat) (acc : nat) (maxLvl : nat) : IO nat :=
  match fuel with
  | O => Ret acc
  | S fuel' =>
      if Nat.leb maxLvl acc then Ret acc
      else
        r <- randomInt 100%int63 ;;
        if ltb r 50%int63 then
          chooseLevel_aux fuel' (S acc) maxLvl
        else
          Ret acc
  end.

Definition chooseLevel : IO nat := chooseLevel_aux maxLevels 0 maxLevels.

Module SkipList.

(* ========================================================================= *)
(*                     Axiomatized Node Type                                 *)
(* ========================================================================= *)

(* Since Rocq doesn't allow recursive types through TVar, we axiomatize
   the node structure and provide extraction rules to C++. *)

Module Node_axioms.
  (* NodeRef is a reference to a node - extracted to shared_ptr<Node<K,V>> *)
  Axiom NodeRef : Type -> Type -> Type.

  (* Node operations *)
  Axiom inewNode : forall {K V : Type}, K -> V -> nat -> STM_axioms.iSTM (NodeRef K V).
  Axiom igetKey : forall {K V : Type}, NodeRef K V -> K.
  Axiom ireadValue : forall {K V : Type}, NodeRef K V -> STM_axioms.iSTM V.
  Axiom iwriteValue : forall {K V : Type}, NodeRef K V -> V -> STM_axioms.iSTM void.
  Axiom igetLevel : forall {K V : Type}, NodeRef K V -> nat.
  Axiom ireadNext : forall {K V : Type}, NodeRef K V -> nat -> STM_axioms.iSTM (option (NodeRef K V)).
  Axiom iwriteNext : forall {K V : Type}, NodeRef K V -> nat -> option (NodeRef K V) -> STM_axioms.iSTM void.
End Node_axioms.

Crane Extract Skip Module Node_axioms.
Import Node_axioms.

(* Wrap axioms in STM monad *)
Definition newNode {K V : Type} (k : K) (v : V) (level : nat) : STM (NodeRef K V) :=
  trigger (inewNode k v level).

Definition getKey {K V : Type} (n : NodeRef K V) : K := igetKey n.

Definition readValue {K V : Type} (n : NodeRef K V) : STM V :=
  trigger (ireadValue n).

Definition writeValue {K V : Type} (n : NodeRef K V) (v : V) : STM void :=
  trigger (iwriteValue n v).

Definition getLevel {K V : Type} (n : NodeRef K V) : nat := igetLevel n.

Definition readNext {K V : Type} (n : NodeRef K V) (level : nat) : STM (option (NodeRef K V)) :=
  trigger (ireadNext n level).

Definition writeNext {K V : Type} (n : NodeRef K V) (level : nat) (next : option (NodeRef K V)) : STM void :=
  trigger (iwriteNext n level next).

(* Find predecessor at a given level *)
(* The function is defined with fuel for Rocq's termination checker. *)

(* Sufficient fuel for any reasonable skip list traversal *)
Definition findPredFuel : nat := 10000.
Crane Extract Inlined Constant findPredFuel => "10000u".

(* ========================================================================= *)
(*                     Path Type (extracts to fixed array)                   *)
(* ========================================================================= *)

(* Path stores predecessors at each level - extracts to std::array for efficiency *)
Module Path_axioms.
  Axiom Path : Type -> Type -> Type.
  Axiom iemptyPath : forall {K V : Type}, STM_axioms.iSTM (Path K V).
  Axiom isetPath : forall {K V : Type}, Path K V -> nat -> NodeRef K V -> STM_axioms.iSTM void.
  Axiom igetPath : forall {K V : Type}, Path K V -> nat -> STM_axioms.iSTM (NodeRef K V).
End Path_axioms.

Crane Extract Skip Module Path_axioms.
Import Path_axioms.

Definition emptyPath {K V : Type} : STM (Path K V) := trigger (@iemptyPath K V).
Definition setPath {K V : Type} (p : Path K V) (lvl : nat) (n : NodeRef K V) : STM void :=
  trigger (isetPath p lvl n).
Definition getPath {K V : Type} (p : Path K V) (lvl : nat) : STM (NodeRef K V) :=
  trigger (igetPath p lvl).

Crane Extract Inlined Constant Path => "SkipPath<%t0, %t1>" From "skipnode.h".
Crane Extract Inlined Constant emptyPath => "SkipPath<%t0, %t1>{}".
Crane Extract Inlined Constant setPath => "%a0.set(%a1, %a2)".
Crane Extract Inlined Constant getPath => "%a0.get(%a1)".

Fixpoint findPred_go {K V : Type} (ltK : K -> K -> bool)
  (fuel : nat) (curr : NodeRef K V) (target : K) (level : nat)
  : STM (NodeRef K V) :=
  match fuel with
  | O => Ret curr  (* Should never happen with sufficient fuel *)
  | S fuel' =>
      nextOpt <- readNext curr level ;;
      match nextOpt with
      | None => Ret curr
      | Some next =>
          if ltK (getKey next) target then
            findPred_go ltK fuel' next target level
          else
            Ret curr
      end
  end.

Definition findPred {K V : Type} (ltK : K -> K -> bool) (curr : NodeRef K V) (target : K) (level : nat)
  : STM (NodeRef K V) :=
  findPred_go ltK findPredFuel curr target level.

(* Extraction rules for Node operations *)
Crane Extract Inlined Constant NodeRef => "std::shared_ptr<SkipNode<%t0, %t1>>" From "skipnode.h".
Crane Extract Inlined Constant newNode => "SkipNode<%t0, %t1>::create(%a0, %a1, %a2)".
Crane Extract Inlined Constant getKey => "%a0->key".
Crane Extract Inlined Constant readValue => "stm::readTVar<%t1>(%a0->value)".
Crane Extract Inlined Constant writeValue => "stm::writeTVar<%t1>(%a0->value, %a1)".
Crane Extract Inlined Constant getLevel => "%a0->level".
(* Read returns shared_ptr, convert to optional for Rocq's option type *)
Crane Extract Inlined Constant readNext => "ptr_to_opt(stm::readTVar<std::shared_ptr<SkipNode<%t0, %t1>>>(%a0->forward[%a1]))".
(* Write takes optional, convert to shared_ptr (None -> nullptr) *)
Crane Extract Inlined Constant writeNext => "stm::writeTVar<std::shared_ptr<SkipNode<%t0, %t1>>>(%a0->forward[%a1], opt_to_ptr(%a2))".

(* ========================================================================= *)
(*                            Skip List Structure                            *)
(* ========================================================================= *)

(* Pair/PairHandle - reference to a node in the list (matches BDE's SkipListPair) *)
(* In our STM context, NodeRef (shared_ptr) serves as the pair reference *)
Definition Pair (K V : Type) := NodeRef K V.

Crane Extract Inlined Constant Pair => "std::shared_ptr<SkipNode<%t0, %t1>>".

Record SkipList (K V : Type) := mkSkipList {
  slHead     : NodeRef K V;      (* Sentinel head node *)
  slMaxLevel : nat;              (* Maximum allowed levels *)
  slLevel    : TVar nat;         (* Current highest level in use *)
  slLength   : TVar nat          (* Number of elements in the list *)
}.

Arguments mkSkipList {K V} _ _ _ _.
Arguments slHead {K V} _.
Arguments slMaxLevel {K V} _.
Arguments slLevel {K V} _.
Arguments slLength {K V} _.

(* ========================================================================= *)
(*                           Core Operations                                 *)
(* ========================================================================= *)

Section Operations.

Variable K V : Type.
Variable ltK : K -> K -> bool.   (* less-than comparison on keys *)
Variable eqK : K -> K -> bool.   (* equality on keys *)

(* Collect update path from current level down to 0 *)
(* Uses Path (fixed-size array) for efficiency *)
Fixpoint findPath_aux (curr : NodeRef K V) (target : K) (level : nat)
  (path : Path K V) : STM (Path K V) :=
  pred <- findPred ltK curr target level ;;
  setPath path level pred ;;
  match level with
  | O => Ret path
  | S level' => findPath_aux pred target level' path
  end.

Definition findPath (sl : SkipList K V) (target : K) : STM (Path K V) :=
  lvl <- readTVar (slLevel sl) ;;
  path <- emptyPath ;;
  findPath_aux (slHead sl) target lvl path.

(* ------------------------------------------------------------------------ *)
(*                              lookup                                      *)
(* ------------------------------------------------------------------------ *)

Definition lookup (k : K) (sl : SkipList K V) : STM (option V) :=
  path <- findPath sl k ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | None => Ret None
  | Some node =>
      if eqK (getKey node) k then
        v <- readValue node ;;
        Ret (Some v)
      else
        Ret None
  end.

(* ------------------------------------------------------------------------ *)
(*                              insert                                      *)
(* ------------------------------------------------------------------------ *)

(* Link new node at one level *)
Definition linkAtLevel (pred newNode : NodeRef K V) (level : nat) : STM void :=
  oldNext <- readNext pred level ;;
  writeNext pred level (Some newNode) ;;
  writeNext newNode level oldNext.

(* Link at all levels from nodeLevel down to 0 *)
Fixpoint linkNode_aux (path : Path K V) (head : NodeRef K V) (newNode : NodeRef K V) (level : nat)
  : STM void :=
  pred <- getPath path level ;;
  (* If path doesn't have this level (returns null), use head *)
  let actualPred := pred in (* Path always returns head for unset levels *)
  linkAtLevel actualPred newNode level ;;
  match level with
  | O => Ret ghost
  | S level' => linkNode_aux path head newNode level'
  end.

(* Ensure path has head node for levels above what findPath found *)
(* Fills from level down to maxLevel (inclusive) *)
Fixpoint extendPath_aux (path : Path K V) (head : NodeRef K V) (level : nat) (maxLevel : nat) : STM void :=
  match level with
  | O => setPath path 0 head
  | S level' =>
      setPath path level head ;;
      (* Continue recursing while level > maxLevel (i.e., level' >= maxLevel) *)
      if Nat.leb maxLevel level' then
        extendPath_aux path head level' maxLevel
      else
        Ret ghost
  end.

Definition extendPath (path : Path K V) (head : NodeRef K V) (needed : nat) (currentMax : nat) : STM void :=
  (* Fill levels from currentMax+1 up to needed-1 with head *)
  (* If needed <= currentMax + 1, there are no new levels to fill *)
  if Nat.leb needed (S currentMax) then Ret ghost
  else
    (* Set levels from needed-1 down to currentMax+1 *)
    extendPath_aux path head (needed - 1) (currentMax + 1).

Definition linkNode (path : Path K V) (head : NodeRef K V) (newNode : NodeRef K V) : STM void :=
  let lvl := getLevel newNode in
  linkNode_aux path head newNode lvl.

Definition insert (k : K) (v : V) (sl : SkipList K V) (newLevel : nat) : STM void :=
  path <- findPath sl k ;;
  curLvl <- readTVar (slLevel sl) ;;
  (* Extend path with head for levels above current slLevel *)
  extendPath path (slHead sl) (S newLevel) curLvl ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | Some existing =>
      if eqK (getKey existing) k then
        writeValue existing v
      else
        newN <- newNode k v newLevel ;;
        linkNode path (slHead sl) newN ;;
        (if Nat.ltb curLvl newLevel then
          writeTVar (slLevel sl) newLevel
        else
          Ret ghost) ;;
        len <- readTVar (slLength sl) ;;
        writeTVar (slLength sl) (S len)
  | None =>
      newN <- newNode k v newLevel ;;
      linkNode path (slHead sl) newN ;;
      (if Nat.ltb curLvl newLevel then
        writeTVar (slLevel sl) newLevel
      else
        Ret ghost) ;;
      len <- readTVar (slLength sl) ;;
      writeTVar (slLength sl) (S len)
  end.

(* ------------------------------------------------------------------------ *)
(*                              remove                                      *)
(* ------------------------------------------------------------------------ *)

Definition unlinkAtLevel (pred target : NodeRef K V) (level : nat) : STM void :=
  targetNext <- readNext target level ;;
  writeNext pred level targetNext.

Fixpoint unlinkNode_aux (path : Path K V) (target : NodeRef K V) (level : nat)
  : STM void :=
  pred <- getPath path level ;;
  unlinkAtLevel pred target level ;;
  match level with
  | O => Ret ghost
  | S level' => unlinkNode_aux path target level'
  end.

Definition unlinkNode (path : Path K V) (target : NodeRef K V) : STM void :=
  let lvl := getLevel target in
  unlinkNode_aux path target lvl.

Definition remove (k : K) (sl : SkipList K V) : STM void :=
  path <- findPath sl k ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | Some node =>
      if eqK (getKey node) k then
        curLvl <- readTVar (slLevel sl) ;;
        (* Extend path for the target node's level *)
        extendPath path (slHead sl) (S (getLevel node)) curLvl ;;
        unlinkNode path node ;;
        len <- readTVar (slLength sl) ;;
        writeTVar (slLength sl) (len - 1)
      else
        Ret ghost
  | None => Ret ghost
  end.

(* ------------------------------------------------------------------------ *)
(*                              minimum                                     *)
(* ------------------------------------------------------------------------ *)

Definition minimum (sl : SkipList K V) : STM (option (K * V)) :=
  firstOpt <- readNext (slHead sl) 0 ;;
  match firstOpt with
  | None => Ret None
  | Some node =>
      v <- readValue node ;;
      Ret (Some (getKey node, v))
  end.

(* ------------------------------------------------------------------------ *)
(*                              member                                      *)
(* ------------------------------------------------------------------------ *)

(* Fast traversal without building path - just finds if key exists *)
Fixpoint findKey_aux (curr : NodeRef K V) (target : K) (level : nat) : STM bool :=
  pred <- findPred ltK curr target level ;;
  match level with
  | O =>
      nextOpt <- readNext pred 0 ;;
      match nextOpt with
      | None => Ret false
      | Some node => Ret (eqK (getKey node) target)
      end
  | S level' => findKey_aux pred target level'
  end.

Definition memberFast (k : K) (sl : SkipList K V) : STM bool :=
  lvl <- readTVar (slLevel sl) ;;
  findKey_aux (slHead sl) k lvl.

(* Original member using lookup - kept for compatibility *)
(* Note: Inlined body to avoid extraction bug with simple function aliases *)
Definition member (k : K) (sl : SkipList K V) : STM bool :=
  lvl <- readTVar (slLevel sl) ;;
  findKey_aux (slHead sl) k lvl.

(* ========================================================================= *)
(*                     BDE-Compatible Operations                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------ *)
(*                         isEmpty / length                                  *)
(* ------------------------------------------------------------------------ *)

Definition isEmpty (sl : SkipList K V) : STM bool :=
  len <- readTVar (slLength sl) ;;
  Ret (Nat.eqb len 0).

Definition length (sl : SkipList K V) : STM nat :=
  readTVar (slLength sl).

(* ------------------------------------------------------------------------ *)
(*                    exists (BDE naming for member)                         *)
(* ------------------------------------------------------------------------ *)

Definition exists_ (k : K) (sl : SkipList K V) : STM bool :=
  lvl <- readTVar (slLevel sl) ;;
  findKey_aux (slHead sl) k lvl.

(* ------------------------------------------------------------------------ *)
(*                         front / back                                      *)
(* ------------------------------------------------------------------------ *)

(* front - Load reference to first item. Returns None if empty. *)
Definition front (sl : SkipList K V) : STM (option (Pair K V)) :=
  readNext (slHead sl) 0.

(* back - Load reference to last item. Requires traversing the list. *)
(* Uses fuel-based traversal to find the last element *)
Fixpoint findLast_aux (fuel : nat) (curr : NodeRef K V) : STM (option (NodeRef K V)) :=
  match fuel with
  | O => Ret (Some curr)
  | S fuel' =>
      nextOpt <- readNext curr 0 ;;
      match nextOpt with
      | None => Ret (Some curr)
      | Some next => findLast_aux fuel' next
      end
  end.

Definition back (sl : SkipList K V) : STM (option (Pair K V)) :=
  firstOpt <- readNext (slHead sl) 0 ;;
  match firstOpt with
  | None => Ret None
  | Some first => findLast_aux findPredFuel first
  end.

(* ------------------------------------------------------------------------ *)
(*                              popFront                                     *)
(* ------------------------------------------------------------------------ *)

(* Helper to unlink first node from head at all levels *)
Fixpoint unlinkFirstFromHead (head node : NodeRef K V) (nodeLevel : nat) (lvl : nat) : STM void :=
  match lvl with
  | O =>
      nodeNext <- readNext node 0 ;;
      writeNext head 0 nodeNext
  | S lvl' =>
      headNext <- readNext head lvl ;;
      (match headNext with
      | Some _ =>
          if Nat.leb lvl nodeLevel then
            nodeNext <- readNext node lvl ;;
            writeNext head lvl nodeNext
          else
            Ret ghost
      | None => Ret ghost
      end) ;;
      unlinkFirstFromHead head node nodeLevel lvl'
  end.

(* Remove and return the first item from the list *)
Definition popFront (sl : SkipList K V) : STM (option (K * V)) :=
  firstOpt <- readNext (slHead sl) 0 ;;
  match firstOpt with
  | None => Ret None
  | Some node =>
      unlinkFirstFromHead (slHead sl) node (getLevel node) (maxLevels - 1) ;;
      len <- readTVar (slLength sl) ;;
      writeTVar (slLength sl) (len - 1) ;;
      v <- readValue node ;;
      Ret (Some (getKey node, v))
  end.

(* ------------------------------------------------------------------------ *)
(*                              removeAll                                    *)
(* ------------------------------------------------------------------------ *)

(* Helper to unlink a node at all levels from head *)
Fixpoint unlinkNodeAtAllLevels (head node : NodeRef K V) (lvl : nat) : STM void :=
  headNext <- readNext head lvl ;;
  (match headNext with
  | Some _ =>
      nodeNext <- readNext node lvl ;;
      writeNext head lvl nodeNext
  | None => Ret ghost
  end) ;;
  match lvl with
  | O => Ret ghost
  | S lvl' => unlinkNodeAtAllLevels head node lvl'
  end.

(* Remove all items from the list - uses accumulator for tail-call optimization *)
Fixpoint removeAll_aux (fuel : nat) (head : NodeRef K V) (maxLvl : nat) (acc : nat) : STM nat :=
  match fuel with
  | O => Ret acc
  | S fuel' =>
      firstOpt <- readNext head 0 ;;
      match firstOpt with
      | None => Ret acc
      | Some node =>
          unlinkNodeAtAllLevels head node maxLvl ;;
          removeAll_aux fuel' head maxLvl (S acc)  (* Tail call with accumulated count *)
      end
  end.

Definition removeAll (sl : SkipList K V) : STM nat :=
  count <- removeAll_aux findPredFuel (slHead sl) (maxLevels - 1) 0 ;;
  writeTVar (slLength sl) 0 ;;
  writeTVar (slLevel sl) 0 ;;
  Ret count.

(* ------------------------------------------------------------------------ *)
(*                              add / addUnique                              *)
(* ------------------------------------------------------------------------ *)

(* add - Add key/data pair to the list (allows duplicates) - renamed from insert *)
Definition add (k : K) (v : V) (sl : SkipList K V) (newLevel : nat) : STM void :=
  path <- findPath sl k ;;
  curLvl <- readTVar (slLevel sl) ;;
  extendPath path (slHead sl) (S newLevel) curLvl ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | Some existing =>
      if eqK (getKey existing) k then
        writeValue existing v
      else
        newN <- newNode k v newLevel ;;
        linkNode path (slHead sl) newN ;;
        (if Nat.ltb curLvl newLevel then
          writeTVar (slLevel sl) newLevel
        else
          Ret ghost) ;;
        len <- readTVar (slLength sl) ;;
        writeTVar (slLength sl) (S len)
  | None =>
      newN <- newNode k v newLevel ;;
      linkNode path (slHead sl) newN ;;
      (if Nat.ltb curLvl newLevel then
        writeTVar (slLevel sl) newLevel
      else
        Ret ghost) ;;
      len <- readTVar (slLength sl) ;;
      writeTVar (slLength sl) (S len)
  end.

(* addUnique - Add only if key doesn't already exist. Returns true on success. *)
Definition addUnique (k : K) (v : V) (sl : SkipList K V) (newLevel : nat) : STM bool :=
  path <- findPath sl k ;;
  curLvl <- readTVar (slLevel sl) ;;
  extendPath path (slHead sl) (S newLevel) curLvl ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | Some existing =>
      if eqK (getKey existing) k then
        Ret false
      else
        newN <- newNode k v newLevel ;;
        linkNode path (slHead sl) newN ;;
        (if Nat.ltb curLvl newLevel then
          writeTVar (slLevel sl) newLevel
        else
          Ret ghost) ;;
        len <- readTVar (slLength sl) ;;
        writeTVar (slLength sl) (S len) ;;
        Ret true
  | None =>
      newN <- newNode k v newLevel ;;
      linkNode path (slHead sl) newN ;;
      (if Nat.ltb curLvl newLevel then
        writeTVar (slLevel sl) newLevel
      else
        Ret ghost) ;;
      len <- readTVar (slLength sl) ;;
      writeTVar (slLength sl) (S len) ;;
      Ret true
  end.

(* ------------------------------------------------------------------------ *)
(*                              find                                         *)
(* ------------------------------------------------------------------------ *)

(* find - Find element by key and return reference to the pair *)
Definition find (k : K) (sl : SkipList K V) : STM (option (Pair K V)) :=
  path <- findPath sl k ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | None => Ret None
  | Some node =>
      if eqK (getKey node) k then
        Ret (Some node)
      else
        Ret None
  end.

(* ------------------------------------------------------------------------ *)
(*                          next / previous                                  *)
(* ------------------------------------------------------------------------ *)

(* next - Get the next element after the given pair *)
Definition next (pair : Pair K V) : STM (option (Pair K V)) :=
  readNext pair 0.

(* previous - Get the previous element before the given pair *)
(* Note: This requires traversing from the head, as skip lists don't have back pointers *)
Fixpoint findPrev_aux (fuel : nat) (curr prev : NodeRef K V) (target : K) : STM (option (NodeRef K V)) :=
  match fuel with
  | O => Ret None
  | S fuel' =>
      nextOpt <- readNext curr 0 ;;
      match nextOpt with
      | None => Ret None
      | Some next =>
          if eqK (getKey next) target then
            Ret (Some curr)
          else
            findPrev_aux fuel' next curr target
      end
  end.

Definition previous (pair : Pair K V) (sl : SkipList K V) : STM (option (Pair K V)) :=
  (* Check if pair is the first element *)
  firstOpt <- readNext (slHead sl) 0 ;;
  match firstOpt with
  | None => Ret None
  | Some first =>
      if eqK (getKey first) (getKey pair) then
        Ret None  (* pair is at front, no previous *)
      else
        findPrev_aux findPredFuel first (slHead sl) (getKey pair)
  end.

(* ------------------------------------------------------------------------ *)
(*                    findLowerBound / findUpperBound                        *)
(* ------------------------------------------------------------------------ *)

(* findLowerBound - Find first element whose key is not less than given key *)
Definition findLowerBound (k : K) (sl : SkipList K V) : STM (option (Pair K V)) :=
  path <- findPath sl k ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | None => Ret None
  | Some node =>
      (* node's key is >= k (since pred's key < k and node is next) *)
      Ret (Some node)
  end.

(* findUpperBound - Find first element whose key is greater than given key *)
Definition findUpperBound (k : K) (sl : SkipList K V) : STM (option (Pair K V)) :=
  path <- findPath sl k ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | None => Ret None
  | Some node =>
      if eqK (getKey node) k then
        (* Key matches, need to get the next one *)
        readNext node 0
      else
        (* Key is already greater *)
        Ret (Some node)
  end.

(* ------------------------------------------------------------------------ *)
(*                            remove (by pair)                               *)
(* ------------------------------------------------------------------------ *)

(* removePair - Remove element identified by a Pair reference *)
Definition removePair (pair : Pair K V) (sl : SkipList K V) : STM bool :=
  let k := getKey pair in
  path <- findPath sl k ;;
  curLvl <- readTVar (slLevel sl) ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | Some node =>
      if eqK (getKey node) k then
        extendPath path (slHead sl) (S (getLevel node)) curLvl ;;
        unlinkNode path node ;;
        len <- readTVar (slLength sl) ;;
        writeTVar (slLength sl) (len - 1) ;;
        Ret true
      else
        Ret false
  | None => Ret false
  end.

(* ------------------------------------------------------------------------ *)
(*                          Pair accessors                                   *)
(* ------------------------------------------------------------------------ *)

(* key - Get the key from a pair *)
Definition key (pair : Pair K V) : K := getKey pair.

(* data - Get the data from a pair *)
Definition data (pair : Pair K V) : STM V := readValue pair.

End Operations.

(* ========================================================================= *)
(*                    BDE-Compatible Type Signatures                         *)
(* ========================================================================= *)

(* Status codes matching bdlcc::SkipList *)
Definition e_SUCCESS   : nat := zero.
Definition e_NOT_FOUND : nat := one.
Definition e_DUPLICATE : nat := two.
Definition e_INVALID   : nat := three.

(* These operations match BDE's type signatures as closely as possible:
   - Return status codes (nat) instead of option types
   - Return pairs (status, result) to simulate output parameters
   - Include newFrontFlag where BDE has it
*)

Section BDECompatible.

Variable K V : Type.
Variable ltK : K -> K -> bool.
Variable eqK : K -> K -> bool.

(* ------------------------------------------------------------------------ *)
(*  int add(PairHandle *result, const KEY& key, const DATA& data,           *)
(*          bool *newFrontFlag = 0);                                        *)
(*  Returns: (result, newFrontFlag)                                         *)
(* ------------------------------------------------------------------------ *)

Definition bde_add (key : K) (data : V) (sl : SkipList K V) (level : nat)
  : STM (Pair K V * bool) :=
  path <- findPath ltK sl key ;;
  curLvl <- readTVar (slLevel sl) ;;
  extendPath path (slHead sl) (S level) curLvl ;;
  (* Check if this will be at front *)
  curFront <- readNext (slHead sl) 0 ;;
  let isNewFront := match curFront with
                    | None => true
                    | Some frontNode => ltK key (getKey frontNode)
                    end in
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | Some existing =>
      if eqK (getKey existing) key then
        writeValue existing data ;;
        Ret (existing, false)  (* Update existing, not new front *)
      else
        newN <- newNode key data level ;;
        linkNode path (slHead sl) newN ;;
        (if Nat.ltb curLvl level then
          writeTVar (slLevel sl) level
        else
          Ret ghost) ;;
        len <- readTVar (slLength sl) ;;
        writeTVar (slLength sl) (S len) ;;
        Ret (newN, isNewFront)
  | None =>
      newN <- newNode key data level ;;
      linkNode path (slHead sl) newN ;;
      (if Nat.ltb curLvl level then
        writeTVar (slLevel sl) level
      else
        Ret ghost) ;;
      len <- readTVar (slLength sl) ;;
      writeTVar (slLength sl) (S len) ;;
      Ret (newN, isNewFront)
  end.

(* ------------------------------------------------------------------------ *)
(*  int addUnique(PairHandle *result, const KEY& key, const DATA& data,     *)
(*                bool *newFrontFlag = 0);                                  *)
(*  Returns: (status, result_opt, newFrontFlag)                             *)
(*  status = e_SUCCESS (0) or e_DUPLICATE (2)                               *)
(* ------------------------------------------------------------------------ *)

Definition bde_addUnique (key : K) (data : V) (sl : SkipList K V) (level : nat)
  : STM (nat * option (Pair K V) * bool) :=
  path <- findPath ltK sl key ;;
  curLvl <- readTVar (slLevel sl) ;;
  extendPath path (slHead sl) (S level) curLvl ;;
  curFront <- readNext (slHead sl) 0 ;;
  let isNewFront := match curFront with
                    | None => true
                    | Some frontNode => ltK key (getKey frontNode)
                    end in
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | Some existing =>
      if eqK (getKey existing) key then
        Ret (e_DUPLICATE, None, false)
      else
        newN <- newNode key data level ;;
        linkNode path (slHead sl) newN ;;
        (if Nat.ltb curLvl level then
          writeTVar (slLevel sl) level
        else
          Ret ghost) ;;
        len <- readTVar (slLength sl) ;;
        writeTVar (slLength sl) (S len) ;;
        Ret (e_SUCCESS, Some newN, isNewFront)
  | None =>
      newN <- newNode key data level ;;
      linkNode path (slHead sl) newN ;;
      (if Nat.ltb curLvl level then
        writeTVar (slLevel sl) level
      else
        Ret ghost) ;;
      len <- readTVar (slLength sl) ;;
      writeTVar (slLength sl) (S len) ;;
      Ret (e_SUCCESS, Some newN, isNewFront)
  end.

(* ------------------------------------------------------------------------ *)
(*  int find(PairHandle *item, const KEY& key) const;                       *)
(*  Returns: (status, item_opt)                                             *)
(*  status = e_SUCCESS (0) or e_NOT_FOUND (1)                               *)
(* ------------------------------------------------------------------------ *)

Definition bde_find (key : K) (sl : SkipList K V) : STM (nat * option (Pair K V)) :=
  path <- findPath ltK sl key ;;
  pred0 <- getPath path 0 ;;
  nextOpt <- readNext pred0 0 ;;
  match nextOpt with
  | None => Ret (e_NOT_FOUND, None)
  | Some node =>
      if eqK (getKey node) key then
        Ret (e_SUCCESS, Some node)
      else
        Ret (e_NOT_FOUND, None)
  end.

(* ------------------------------------------------------------------------ *)
(*  int front(PairHandle *front) const;                                     *)
(*  Returns: (status, front_opt)                                            *)
(* ------------------------------------------------------------------------ *)

Definition bde_front (sl : SkipList K V) : STM (nat * option (Pair K V)) :=
  frontOpt <- readNext (slHead sl) 0 ;;
  match frontOpt with
  | None => Ret (e_NOT_FOUND, None)
  | Some node => Ret (e_SUCCESS, Some node)
  end.

(* ------------------------------------------------------------------------ *)
(*  int back(PairHandle *back) const;                                       *)
(*  Returns: (status, back_opt)                                             *)
(* ------------------------------------------------------------------------ *)

Definition bde_back (sl : SkipList K V) : STM (nat * option (Pair K V)) :=
  backOpt <- back sl ;;
  match backOpt with
  | None => Ret (e_NOT_FOUND, None)
  | Some node => Ret (e_SUCCESS, Some node)
  end.

(* ------------------------------------------------------------------------ *)
(*  int popFront(PairHandle *item = 0);                                     *)
(*  Returns: (status, item_opt)                                             *)
(* ------------------------------------------------------------------------ *)

Definition bde_popFront (sl : SkipList K V) : STM (nat * option (Pair K V)) :=
  firstOpt <- readNext (slHead sl) 0 ;;
  match firstOpt with
  | None => Ret (e_NOT_FOUND, None)
  | Some node =>
      unlinkFirstFromHead (slHead sl) node (getLevel node) (maxLevels - 1) ;;
      len <- readTVar (slLength sl) ;;
      writeTVar (slLength sl) (len - 1) ;;
      Ret (e_SUCCESS, Some node)
  end.

(* ------------------------------------------------------------------------ *)
(*  int remove(const Pair *reference);                                      *)
(*  Returns: status                                                         *)
(* ------------------------------------------------------------------------ *)

Definition bde_remove (pair : Pair K V) (sl : SkipList K V) : STM nat :=
  result <- removePair ltK eqK pair sl ;;
  if result then Ret e_SUCCESS else Ret e_NOT_FOUND.

(* ------------------------------------------------------------------------ *)
(*  int removeAll();                                                        *)
(*  Returns: count of removed items                                         *)
(* ------------------------------------------------------------------------ *)

Definition bde_removeAll (sl : SkipList K V) : STM nat :=
  removeAll sl.

(* ------------------------------------------------------------------------ *)
(*  bool exists(const KEY& key) const;                                      *)
(* ------------------------------------------------------------------------ *)

Definition bde_exists (key : K) (sl : SkipList K V) : STM bool :=
  lvl <- readTVar (slLevel sl) ;;
  findKey_aux ltK eqK (slHead sl) key lvl.

(* ------------------------------------------------------------------------ *)
(*  bool isEmpty() const;                                                   *)
(* ------------------------------------------------------------------------ *)

Definition bde_isEmpty (sl : SkipList K V) : STM bool :=
  isEmpty sl.

(* ------------------------------------------------------------------------ *)
(*  int length() const;                                                     *)
(* ------------------------------------------------------------------------ *)

Definition bde_length (sl : SkipList K V) : STM nat :=
  length sl.

(* ------------------------------------------------------------------------ *)
(*  int next(PairHandle *next, const Pair *reference) const;                *)
(*  Returns: (status, next_opt)                                             *)
(* ------------------------------------------------------------------------ *)

Definition bde_next (pair : Pair K V) : STM (nat * option (Pair K V)) :=
  nextOpt <- next pair ;;
  match nextOpt with
  | None => Ret (e_NOT_FOUND, None)
  | Some node => Ret (e_SUCCESS, Some node)
  end.

(* ------------------------------------------------------------------------ *)
(*  int previous(PairHandle *prevPair, const Pair *reference) const;        *)
(*  Returns: (status, prev_opt)                                             *)
(* ------------------------------------------------------------------------ *)

Definition bde_previous (pair : Pair K V) (sl : SkipList K V) : STM (nat * option (Pair K V)) :=
  prevOpt <- previous eqK pair sl ;;
  match prevOpt with
  | None => Ret (e_NOT_FOUND, None)
  | Some node => Ret (e_SUCCESS, Some node)
  end.

(* ------------------------------------------------------------------------ *)
(*  int findLowerBound(PairHandle *item, const KEY& key) const;             *)
(*  Returns: (status, item_opt)                                             *)
(* ------------------------------------------------------------------------ *)

Definition bde_findLowerBound (key : K) (sl : SkipList K V) : STM (nat * option (Pair K V)) :=
  result <- findLowerBound ltK key sl ;;
  match result with
  | None => Ret (e_NOT_FOUND, None)
  | Some node => Ret (e_SUCCESS, Some node)
  end.

(* ------------------------------------------------------------------------ *)
(*  int findUpperBound(PairHandle *item, const KEY& key) const;             *)
(*  Returns: (status, item_opt)                                             *)
(* ------------------------------------------------------------------------ *)

Definition bde_findUpperBound (key : K) (sl : SkipList K V) : STM (nat * option (Pair K V)) :=
  result <- findUpperBound ltK eqK key sl ;;
  match result with
  | None => Ret (e_NOT_FOUND, None)
  | Some node => Ret (e_SUCCESS, Some node)
  end.

End BDECompatible.

(* ========================================================================= *)
(*                            Construction                                   *)
(* ========================================================================= *)

Definition create {K V : Type} (dummyKey : K) (dummyVal : V) : STM (SkipList K V) :=
  headNode <- newNode dummyKey dummyVal (maxLevels - 1) ;;
  lvlTV <- newTVar 0 ;;
  lenTV <- newTVar 0 ;;
  Ret (mkSkipList headNode maxLevels lvlTV lenTV).

Definition createIO {K V : Type} (dummyKey : K) (dummyVal : V) : IO (SkipList K V) :=
  atomically (create dummyKey dummyVal).

End SkipList.

(* ========================================================================= *)
(*                              Test Module                                  *)
(* ========================================================================= *)

Module skiplist_test.
Import SkipList.

Definition nat_lt (x y : nat) : bool := Nat.ltb x y.
Definition nat_eq (x y : nat) : bool := Nat.eqb x y.

(* STM test functions *)
Definition stm_test_insert_lookup (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  (* Use multiple levels to test skip list structure *)
  insert nat_lt nat_eq five fifty sl two ;;
  insert nat_lt nat_eq three thirty sl one  ;;
  insert nat_lt nat_eq seven seventy sl 0 ;;
  insert nat_lt nat_eq one ten sl one  ;;

  v5 <- lookup nat_lt nat_eq five sl ;;
  v3 <- lookup nat_lt nat_eq three sl ;;
  v7 <- lookup nat_lt nat_eq seven sl ;;
  v1 <- lookup nat_lt nat_eq one  sl ;;
  v9 <- lookup nat_lt nat_eq nine sl ;;

  let c1 := match v5 with Some n => Nat.eqb n fifty | _ => false end in
  let c2 := match v3 with Some n => Nat.eqb n thirty | _ => false end in
  let c3 := match v7 with Some n => Nat.eqb n seventy | _ => false end in
  let c4 := match v1 with Some n => Nat.eqb n ten | _ => false end in
  let c5 := match v9 with None => true | _ => false end in

  Ret (andb c1 (andb c2 (andb c3 (andb c4 c5)))).

Definition stm_test_delete (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  (* Use multiple levels for delete test too *)
  insert nat_lt nat_eq five fifty sl two ;;
  insert nat_lt nat_eq three thirty sl one ;;
  insert nat_lt nat_eq seven seventy sl 0 ;;

  (* Delete node at level 2 *)
  remove nat_lt nat_eq five sl ;;

  v5 <- lookup nat_lt nat_eq five sl ;;
  v3 <- lookup nat_lt nat_eq three sl ;;
  v7 <- lookup nat_lt nat_eq seven sl ;;

  let c1 := match v5 with None => true | _ => false end in
  let c2 := match v3 with Some n => Nat.eqb n thirty | _ => false end in
  let c3 := match v7 with Some n => Nat.eqb n seventy | _ => false end in

  Ret (andb c1 (andb c2 c3)).

Definition fivehundred : nat := 500.
Crane Extract Inlined Constant fivehundred => "500u".

Definition stm_test_update (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq five fifty sl 0 ;;
  insert nat_lt nat_eq five fivehundred  sl 0 ;;

  v <- lookup nat_lt nat_eq five sl ;;
  Ret (match v with Some n => Nat.eqb n fivehundred | _ => false end).

Definition stm_test_minimum (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq five fifty sl 0 ;;
  insert nat_lt nat_eq three thirty sl 0 ;;
  insert nat_lt nat_eq seven seventy sl 0 ;;

  minOpt <- minimum sl ;;
  Ret (match minOpt with
       | Some (k, v) => andb (Nat.eqb k three) (Nat.eqb v thirty)
       | _ => false
       end).

(* BDE-compatible operation tests *)

Definition stm_test_length_isEmpty (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  empty1 <- isEmpty sl ;;
  len1 <- length sl ;;
  insert nat_lt nat_eq five fifty sl 0 ;;
  insert nat_lt nat_eq three thirty sl 0 ;;
  empty2 <- isEmpty sl ;;
  len2 <- length sl ;;
  let c1 := empty1 in
  let c2 := Nat.eqb len1 0 in
  let c3 := negb empty2 in
  let c4 := Nat.eqb len2 two in
  Ret (andb c1 (andb c2 (andb c3 c4))).

Definition stm_test_front_back (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq five fifty sl 0 ;;
  insert nat_lt nat_eq three thirty sl 0 ;;
  insert nat_lt nat_eq seven seventy sl 0 ;;
  frontOpt <- front sl ;;
  backOpt <- back sl ;;
  let c1 := match frontOpt with
            | Some p => Nat.eqb (key p) 3
            | None => false
            end in
  let c2 := match backOpt with
            | Some p => Nat.eqb (key p) 7
            | None => false
            end in
  Ret (andb c1 c2).

Definition stm_test_popFront (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq five fifty sl 0 ;;
  insert nat_lt nat_eq three thirty sl 0 ;;
  insert nat_lt nat_eq seven seventy sl 0 ;;
  pop1 <- popFront sl ;;
  pop2 <- popFront sl ;;
  len <- length sl ;;
  let c1 := match pop1 with Some (k, v) => andb (Nat.eqb k three) (Nat.eqb v thirty) | _ => false end in
  let c2 := match pop2 with Some (k, v) => andb (Nat.eqb k five) (Nat.eqb v fifty) | _ => false end in
  let c3 := Nat.eqb len one  in
  Ret (andb c1 (andb c2 c3)).

Definition stm_test_addUnique (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  r1 <- addUnique nat_lt nat_eq five fifty sl 0 ;;
  r2 <- addUnique nat_lt nat_eq five fivehundred  sl 0 ;;  (* Should fail - key exists *)
  r3 <- addUnique nat_lt nat_eq three thirty sl 0 ;;
  v5 <- lookup nat_lt nat_eq five sl ;;
  len <- length sl ;;
  let c1 := r1 in
  let c2 := negb r2 in
  let c3 := r3 in
  let c4 := match v5 with Some n => Nat.eqb n fifty | _ => false end in (* Value unchanged *)
  let c5 := Nat.eqb len two in
  Ret (andb c1 (andb c2 (andb c3 (andb c4 c5)))).

Definition stm_test_find (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq five fifty sl 0 ;;
  insert nat_lt nat_eq three thirty sl 0 ;;
  pairOpt <- find nat_lt nat_eq five sl ;;
  noneOpt <- find nat_lt nat_eq nine sl ;;
  let c1 := match pairOpt with
            | Some p =>
                let k := key p in
                Nat.eqb k five
            | None => false
            end in
  let c2 := match noneOpt with None => true | _ => false end in
  Ret (andb c1 c2).

Definition stm_test_navigation (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq one ten sl 0 ;;
  insert nat_lt nat_eq three thirty sl 0 ;;
  insert nat_lt nat_eq five fifty sl 0 ;;
  frontOpt <- front sl ;;
  match frontOpt with
  | None => Ret false
  | Some first =>
      nextOpt <- next first ;;
      match nextOpt with
      | None => Ret false
      | Some second =>
          prevOpt <- previous nat_eq second sl ;;
          let c1 := Nat.eqb (key first) one in
          let c2 := Nat.eqb (key second) three in
          let c3 := match prevOpt with
                    | Some p => Nat.eqb (key p) one
                    | None => false
                    end in
          Ret (andb c1 (andb c2 c3))
      end
  end.

Definition stm_test_bounds (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq two twenty sl 0 ;;
  insert nat_lt nat_eq four forty sl 0 ;;
  insert nat_lt nat_eq six sixty sl 0 ;;
  (* findLowerBound three should return 4 (first >= 3) *)
  lb3 <- findLowerBound nat_lt three sl ;;
  (* findLowerBound 4 should return 4 (first >= 4) *)
  lb4 <- findLowerBound nat_lt four sl ;;
  (* findUpperBound 4 should return 6 (first > 4) *)
  ub4 <- findUpperBound nat_lt nat_eq four sl ;;
  let c1 := match lb3 with Some p => Nat.eqb (key p) four | None => false end in
  let c2 := match lb4 with Some p => Nat.eqb (key p) four | None => false end in
  let c3 := match ub4 with Some p => Nat.eqb (key p) six | None => false end in
  Ret (andb c1 (andb c2 c3)).

Definition stm_test_removeAll (_ : void) : STM bool :=
  sl <- create 0 0 ;;
  insert nat_lt nat_eq five fifty sl 0 ;;
  insert nat_lt nat_eq three thirty sl 0 ;;
  insert nat_lt nat_eq seven seventy sl 0 ;;
  count <- removeAll sl ;;
  empty <- isEmpty sl ;;
  len <- length sl ;;
  let c1 := Nat.eqb count three in
  let c2 := empty in
  let c3 := Nat.eqb len 0 in
  Ret (andb c1 (andb c2 c3)).

(* BDE-compatible API test *)
Definition stm_test_bde_api (_ : void) : STM bool :=
  sl <- create 0 0 ;;

  (* Test bde_add with newFrontFlag *)
  result1 <- bde_add nat_lt nat_eq five fifty sl 0 ;;
  let '(pair1, front1) := result1 in

  result2 <- bde_add nat_lt nat_eq three thirty sl 0 ;;
  let '(pair2, front2) := result2 in

  result3 <- bde_add nat_lt nat_eq seven seventy sl 0 ;;
  let '(pair3, front3) := result3 in

  (* First insert should be front, second should also be front (3 < 5), third not *)
  let c1 := front1 in
  let c2 := front2 in
  let c3 := negb front3 in

  (* Test bde_find with status codes *)
  findResult <- bde_find nat_lt nat_eq five sl ;;
  let '(status1, item1) := findResult in
  let c4 := Nat.eqb status1 e_SUCCESS in

  findResult2 <- bde_find nat_lt nat_eq nine sl ;;
  let '(status2, item2) := findResult2 in
  let c5 := Nat.eqb status2 e_NOT_FOUND in

  (* Test bde_addUnique with duplicate detection *)
  uniqueResult <- bde_addUnique nat_lt nat_eq five fivehundred sl 0 ;;
  let '(status3, _, _) := uniqueResult in
  let c6 := Nat.eqb status3 e_DUPLICATE in

  (* Test bde_front/bde_back - these don't use ltK/eqK *)
  frontResult <- bde_front sl ;;
  let '(status4, frontItem) := frontResult in
  let c7 := Nat.eqb status4 e_SUCCESS in
  let c8 := match frontItem with
            | Some p => Nat.eqb (key p) three
            | None => false
            end in

  backResult <- bde_back sl ;;
  let '(status5, backItem) := backResult in
  let c9 := Nat.eqb status5 e_SUCCESS in
  let c10 := match backItem with
             | Some p => Nat.eqb (key p) seven
             | None => false
             end in

  Ret (andb c1 (andb c2 (andb c3 (andb c4 (andb c5 (andb c6 (andb c7 (andb c8 (andb c9 c10))))))))).

(* IO wrappers *)
Definition test_insert_lookup (_ : void) : IO bool :=
  atomically (stm_test_insert_lookup ghost).

Definition test_delete (_ : void) : IO bool :=
  atomically (stm_test_delete ghost).

Definition test_update (_ : void) : IO bool :=
  atomically (stm_test_update ghost).

Definition test_minimum (_ : void) : IO bool :=
  atomically (stm_test_minimum ghost).

Definition test_length_isEmpty (_ : void) : IO bool :=
  atomically (stm_test_length_isEmpty ghost).

Definition test_front_back (_ : void) : IO bool :=
  atomically (stm_test_front_back ghost).

Definition test_popFront (_ : void) : IO bool :=
  atomically (stm_test_popFront ghost).

Definition test_addUnique (_ : void) : IO bool :=
  atomically (stm_test_addUnique ghost).

Definition test_find (_ : void) : IO bool :=
  atomically (stm_test_find ghost).

Definition test_navigation (_ : void) : IO bool :=
  atomically (stm_test_navigation ghost).

Definition test_bounds (_ : void) : IO bool :=
  atomically (stm_test_bounds ghost).

Definition test_removeAll (_ : void) : IO bool :=
  atomically (stm_test_removeAll ghost).

Definition test_bde_api (_ : void) : IO bool :=
  atomically (stm_test_bde_api ghost).

Definition run_tests : IO nat :=
  r1 <- test_insert_lookup ghost ;;
  r2 <- test_delete ghost ;;
  r3 <- test_update ghost ;;
  r4 <- test_minimum ghost ;;
  r5 <- test_length_isEmpty ghost ;;
  r6 <- test_front_back ghost ;;
  r7 <- test_popFront ghost ;;
  r8 <- test_addUnique ghost ;;
  r9 <- test_find ghost ;;
  r10 <- test_navigation ghost ;;
  r11 <- test_bounds ghost ;;
  r12 <- test_removeAll ghost ;;
  r13 <- test_bde_api ghost ;;
  let passed := (if r1 then one else zero) +
                (if r2 then one else zero) +
                (if r3 then one else zero) +
                (if r4 then one else zero) +
                (if r5 then one else zero) +
                (if r6 then one else zero) +
                (if r7 then one else zero) +
                (if r8 then one else zero) +
                (if r9 then one else zero) +
                (if r10 then one else zero) +
                (if r11 then one else zero) +
                (if r12 then one else zero) +
                (if r13 then one else zero) in
  Ret passed.

End skiplist_test.

(* Extract both modules - SkipList module contains the TSkipList record, skiplist_test has tests *)
Crane Extraction "skiplist" SkipList skiplist_test.
