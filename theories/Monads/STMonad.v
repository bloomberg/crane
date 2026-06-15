(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

From Stdlib Require Import
  Arith.PeanoNat
  Arith.Peano_dec
  Init.Peano
  List
  Morphisms
  RelationClasses
  Relation_Definitions
  Setoid
  Strings.String
  Classes.EquivDec
.

From Crane Require Import Monads.ITree Utils.HMap Utils.HAList Extraction.
From ExtLib Require Import
  CmpDec
  Data.Bool
  Data.List
  Data.Monads.EitherMonad
  Data.Pair
  Data.String
  Data.Option
  Structures.Functor
  Structures.Traversable
  Structures.Reducible
.

(* NOTE: *must* import this before the ITree Eq.Paco2 import.*)
From Paco Require Import paco.

From ITree Require Import
  Basics.HeterogeneousRelations
  Eq.Paco2
  Events.Exception
  Events.FailFacts
  Events.MapDefault
  Events.MapDefaultFacts
  Events.State
  Events.StateFacts
  ITree
  ITreeFacts
.

Import Monads.
Import ListNotations.
Import ProperNotations.
Local Open Scope monad_scope.
Local Open Scope string_scope.



(* Used for runtime checks, though an ideal impl won't need these. *)

Variant Err : Type :=
| Error (x : string) : Err.

Definition failwith
  {E : Type -> Type} `{exceptE Err -< E}
  {A:Type} (s:string) : itree E A := throw (Error s).


(* Modeled after Ix type in https://hackage.haskell.org/package/base-4.18.1.0/docs/Data-Ix.html#t:Ix *)
Class Ix (T : Type)
  (ltu : T -> T -> Prop) (* lte *)
  : Type :=
  {
    (* The list of values defined in the range, defined inclusively *)
    range : T -> T -> list T; 

    (* diverge from haskell in using error type *)
    index : T -> T -> T -> option nat; 

    (* decidable equality over the range *)
    inRange : T -> T -> T -> Prop; (* NOTE: bool here? *)

    (* the size of the elements in the range *)
    rangeSize : T -> T -> nat;

    (* conversion to nats *)
    toNat : T -> nat;

    (* conversion from nats *)
    fromNat : nat -> T;

    (* a constructor for an index plus one. *)
    suc : T -> T;

    (* subtraction of two indices *)
    sub: T -> T -> T;

    (* function that gives max between indices. *)
    max : T -> T -> T;

    (* zero value, least value to compare with. *)
    zero : T; 
  }.

#[export] Instance cmp_dec_nat : CmpDec eq Nat.le := {| cmp_dec := Nat.compare |}.
#[export] Instance cmp_dec_correct : CmpDec_Correct cmp_dec_nat.
  econstructor. intros.
  destruct (cmp_dec x y) eqn:Heq
  + inversion Heq.
    apply Nat.compare_eq_iff; assumption.
  + inversion Heq. 
    apply Nat.compare_le_iff.
    unfold not.
    intros HG.
    destruct (x ?= y)%nat. 
    * inversion H0.
    * inversion HG.
    * inversion H0.
  + inversion Heq. 
    specialize (Nat.compare_gt_iff x y) as Hgt.
    destruct Hgt.
    * specialize (H H0).
      apply (Nat.lt_le_incl). assumption.
  Qed.


#[export] Instance nat_ix : Ix nat Nat.le :=
  {|
    range := fun fp sp : nat => seq fp ((1 + sp) - fp);
    index := fun (fp sp : nat) (i : nat) =>
               if andb (Nat.leb fp i) (Nat.leb i (sp))
               then Some (i - fp)
               else None;
    inRange := 
      fun (fp sp : nat) (i : nat) => Nat.le fp i /\ Nat.le i sp;
    rangeSize := fun fp sp : nat => (1 + sp) - fp;
    
    (* needed to generate new indices *)
    suc := Datatypes.S; 
    sub := Nat.sub;
    max := Nat.max; 
    zero := 0;
    toNat := fun n : nat => n;
    fromNat := fun n : nat => n;
  |}.


(* taken from https://hackage.haskell.org/package/base-4.18.1.0/docs/Data-Ix.html#t:Ix*)
Definition option_map_list
  {A B : Type}
  (l : list (option A))
  (f : A -> B -> B)
  (def : B)
  : option B :=
fold (fun (next : option A) (acc : option B) => match next with
                                                | Some a => option_map (f a) acc
                                                | None => None
                                                end)
  (Some def) l.

Class Ix_Correct (T : Type)
  (ltu : T -> T -> Prop) 
  (HI : @Ix T ltu)
  {CD : @CmpDec T eq ltu}
  {CDC : @CmpDec_Correct T eq ltu CD}
  {EQD : EqDec T eq} 
  {RD : @RelDec.RelDec T eq}
  : Type := 
  { 
    inRange_implies_elem : forall (l u i : T),
      inRange l u i <-> (In i (range l u)); 

    (* range (l,u) !! index (l,u) i == i, when inRange (l,u) i *)
    inRange_elems_are_indexable: forall (l u v : T) (i : nat),
      index l u v = Some i ->
      inRange l u v -> (* TODO: superflous precond?*)
      List.nth_error (range l u) i = Some v;


    (* map (index (l,u)) (range (l,u))) == [0..rangeSize (l,u)-1] *)
    map_over_indices_makes_incr_seq: forall (fp sp : T),
      List.map (index fp sp) (range fp sp)
      =
      List.map Some (seq 0 (rangeSize fp sp));


    (* rangeSize (l,u) == length (range (l,u)) *)
    rangeSize_is_length_of_range : forall (fp sp : T),
      rangeSize fp sp = length (range fp sp);
      
  }.

From Stdlib Require Import Lia.

Lemma add_sub_le n m : n <= m -> n + (m - n) = m.
Proof. lia. Qed.

(* TODO: move into nat_ix_correct. unhelpful out here. *)
Lemma in_seq_iff l u i :
  In i (seq l (1 + u - l)) <-> l <= i /\ i <= u.
Proof.
  destruct (Nat.le_gt_cases l (1 + u)) as [Hle|Hgt].
  - rewrite in_seq.
    enough (l + (1 + u - l) = 1 + u) as -> by lia.
    apply add_sub_le. exact Hle.
  - replace (1 + u - l) with 0 by lia. simpl.
    split; [tauto | lia].
Qed.

#[export,refine] Instance nat_ix_correct : Ix_Correct nat Nat.le nat_ix :=
  {|
    inRange_implies_elem := _;
    inRange_elems_are_indexable := _;
    map_over_indices_makes_incr_seq := _;
    rangeSize_is_length_of_range := _
  |}.
- intros l u i. exact (iff_sym (in_seq_iff l u i)).
- intros l u v i Hidx [Hl Hu].
  unfold index, range, nat_ix in *. simpl fst in *. simpl snd in *.
  destruct (Nat.leb l v) eqn:Elv; [|discriminate].
  destruct (Nat.leb v u) eqn:Evu; simpl andb in Hidx; [|discriminate].
  inversion Hidx; subst; clear Hidx.
  apply Nat.leb_le in Elv. apply Nat.leb_le in Evu.
  rewrite nth_error_seq.
  replace ((v - l <? 1 + u - l)%nat) with true
    by (symmetry; apply Nat.ltb_lt; lia).
  f_equal. apply add_sub_le. lia.
- intros l u. unfold index, range, rangeSize, nat_ix. simpl fst. simpl snd.
  set (n := 1 + u - l).
  erewrite List.map_ext_in.
  2: { intros a Ha. apply in_seq in Ha.
       destruct (Nat.leb l a) eqn:E1; [| apply Nat.leb_nle in E1; lia].
       destruct (Nat.leb a u) eqn:E2; [| apply Nat.leb_nle in E2; lia].
       simpl. reflexivity. }
  cut (forall k, List.map (fun i => Some (i - l)) (seq (l + k) n)
                 = List.map Some (seq k n)).
  { intro H. specialize (H 0). rewrite Nat.add_0_r in H. exact H. }
  induction n as [|n' IHn']; intro k.
  + reflexivity.
  + simpl. f_equal.
    * f_equal. lia.
    * replace (S (l + k)) with (l + S k) by lia. apply IHn'.
- intros l u. unfold rangeSize, range, nat_ix. simpl.
  rewrite length_seq. reflexivity.
Qed.

Class STRefClass (T : Type) : Type :=
  {
    STRef : forall S A : Type, Type;
    mkSTRef : forall S A : Type, T -> STRef S A;
    STRefToIx : forall S A : Type, STRef S A -> T;
  }.


Section STRefNatDefs.

  Variable (T : Type).
  

  Variant STRefNat : Type -> Type -> Type :=
  | MkSTRef (S A : Type) (idx : nat) : STRefNat S A.

  
  Definition STRefToIxNat (S A : Type) (ref : STRefNat S A) : nat :=
   match ref with
   | MkSTRef _ _ idx => idx
   end. 

  Variant STArray (S A : Type) : Type :=
    | MkSTArray (base lo hi : T) : STArray S A.

  Definition stArrayBase {S A} (arr : STArray S A) : T :=
    match arr with MkSTArray _ _ base _ _ => base end.

  Definition stArrayBounds {S A} (arr : STArray S A) : T * T :=
    match arr with MkSTArray _ _ _ lo hi => (lo, hi) end.

End STRefNatDefs.

#[export] Instance nat_ix_stref : STRefClass nat :=
  {| STRef := STRefNat;
    mkSTRef := MkSTRef ;
    STRefToIx := STRefToIxNat |}.

Section STEventDefine.  
  Variable (T : Type).
  Context `{STRefClass T}.

  Variant STEvent (S : Type) (V : T -> Type) : Type -> Type :=
    | NewSTRef (idx : T) (v : V idx) : STEvent S V (STRef S (V idx))
    | ReadSTRef (idx : T) : STRef S (V idx) -> STEvent S V (V idx)
    | WriteSTRef (idx : T) : STRef S (V idx) -> (V idx) -> STEvent S V unit
    | NewArray (idx : T) (lo hi : T) (def : V idx) 
      : STEvent S V (STArray T S (V idx))
    | NewListArray (idx : T) (lo hi : T) (elems : list (V idx))
      : STEvent S V (STArray T S (V idx))
    | ReadArray (idx : T) : STArray T S (V idx) -> T -> STEvent S V (V idx)
    | WriteArray (idx : T) : STArray T S (V idx) -> T -> V idx -> STEvent S V unit
    | GetElems (idx : T) : STArray T S (V idx) -> STEvent S V (list (V idx))
  .

End STEventDefine.
  
  
Section Translation.

  Context {E : Type -> Type}.
  Context {T S : Type}.
  Context (ltu : T -> T -> Prop).
  Context `{Ix_Correct T ltu}.
  Context `{STRefClass T}.
  Context {V : T -> Type}.
  Context `{STEvent T S V -< E}. 
  Context `{exceptE Err -< E}.
  

  (* Smart constructors  *)

  (* NOTE: explicit index here because we cannot infer it automatically, yet. *)
  Definition newSTRef (idx : T) (v : (V idx)) : itree E (STRef S (V idx)) :=
    trigger (NewSTRef T S V idx v).

  Definition readSTRef {idx : T} (ref : STRef S (V idx)) : itree E (V idx) :=
    trigger (ReadSTRef T S V idx ref).

  Definition writeSTRef {idx : T} (ref : STRef S (V idx)) (a : (V idx)) : itree E unit :=
    trigger (WriteSTRef T S V idx ref a).

  Definition newArray (idx : T) (lo hi : T) (def : V idx)
    : itree E (STArray T S (V idx)) :=
    trigger (NewArray T S V idx lo hi def).

  (* NOTE: explicit index here because we cannot infer it. *)
  Definition newListArray (idx : T) (lo hi : T) (elems : list (V idx))
    : itree E (STArray T S (V idx)) :=
    trigger (NewListArray T S V idx lo hi elems).

  Definition readArray {idx : T} (arr : STArray T S (V idx)) (i : T)
    : itree E (V idx) :=
    trigger (ReadArray T S V idx arr i).

  Definition writeArray {idx : T} (arr : STArray T S (V idx)) (i : T) (v : V idx)
    : itree E unit :=
    trigger (WriteArray T S V idx arr i v).

  Definition getElems {idx : T} (arr : STArray T S (V idx))
    : itree E (list (V idx)) :=
    trigger (GetElems T S V idx arr).

  
  (* key type definitions *)

  Definition pkey (J K : Type) := (J * K)%type.
  Definition pkey_type {J K} (V : K -> Type) (pk : pkey J K) := V (snd pk).
  Definition idx_key := pkey T. 
  Definition idx_key_type {K} (V : K -> Type) (ik : idx_key K) := V (snd ik).


  Context {M : Type}.
  Context `{HMap (idx_key T) (idx_key_type V) M}.
  Context `{Foldable M (sigT (idx_key_type V))}.

  Fixpoint suc_n (n : nat) (t : T) : T :=
    match n with
    | O => t
    | Datatypes.S n' => suc (suc_n n' t)
    end.

  Definition arr_key (idx : T) (arr : STArray T S (V idx)) (i : T)
    : option T :=
    let 'MkSTArray _ _ _ base fb sb := arr in 
    match index fb sb i with
    | Some n => Some (suc_n n base)
    | None => None
    end.

  Definition arr_lookup (idx : T) (arr : STArray T S (V idx)) (i : T) (mem : M)
    : option (V idx) :=
    match arr_key idx arr i with
    | Some key => lookup (key, idx) mem
    | None => None
    end.

  (* The handler for STEvents itself *)
  Definition handle_STEvent `{EqDec T eq} 
    : forall (A : Type), STEvent T S V A -> stateT M (itree E) A :=
    fun _ e mem =>
    match e with
    | NewSTRef _ _ _ idx v =>
        let n := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem)
        in Ret (add (n, idx) v mem, mkSTRef S (V idx) idx)
    | ReadSTRef _ _ _ idx s =>
        match lookup (STRefToIx S (V idx) s, idx) mem with
        | Some v => Ret (mem, v)
        | None => failwith "Lookup failed!"
        end
    | WriteSTRef _ _ _ idx s v => Ret (add (STRefToIx S (V idx) s, idx) v mem, tt)
    | NewArray _ _ _ idx lo hi def =>
        let base := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem) in
        let positions := range lo hi in
        let fix fill (ps : list T) (m : M) (key : T) {struct ps} : M * T :=
        match ps with
        | nil => (m, key) 
        | _ :: rest => fill rest (add (key, idx) def m) (suc key)
        end in
        let (mem', _ ) := fill positions mem base in
        Ret (mem', MkSTArray T S (V idx) base lo hi)
    | NewListArray _ _ _ idx lo hi elems =>
        let base := suc (fold (fun '(existT _ (n, _) _) (acc : T) => max n acc) zero mem) in
        let fix fill (es : list (V idx)) (m : M) (key : T) {struct es} : M * T :=
          match es with
          | nil => (m, key)
          | v :: rest => fill rest (add (key, idx) v m) (suc key)
          end in
        let '(mem', _) := fill elems mem base in
        Ret (mem', MkSTArray T S (V idx) base lo hi)
    | ReadArray _ _ _ idx arr i =>
        match arr_lookup idx arr i mem with
        | Some v => Ret (mem, v)
        | None => failwith "Array read failed"
        end
    | WriteArray _ _ _ idx arr i v =>
      match arr_key idx arr i with
      | Some key => Ret (add (key, idx) v mem, tt)
      | None => failwith "Array index out of range"
      end
    | GetElems _ _ _ idx arr =>
        let '(fb,sb) := stArrayBounds T arr in
        let positions := range fb sb in
        let fix collect (ps : list T) : option (list (V idx)) :=
          match ps with
          | nil => Some nil
          | p :: rest =>
            match arr_lookup idx arr p mem with
            | Some v =>
              match collect rest with
              | Some elems => Some (v :: elems)
              | None => None
              end
            | None => None
            end
          end in
        match collect positions with
        | Some elems => Ret (mem, elems)
        | None => failwith "Array getElems failed"
        end
    end.

(* Interpretation in Rocq *)

  Definition handle_STEvent_leave_rest
    (A : Type) (e : (STEvent T S V +' E) A)
    : stateT M (itree (E)) A :=
    match e with
    | inl1 e0 => handle_STEvent A e0
    | inr1 e0 => fun st : M => r <- trigger e0;; Ret (st, r)
    end.
  
  #[local] Instance hmap_from_idx :
    HMap T V (halist T V) := @HMap_halist T V eq_equivalence _.

  #[local] Instance map_idx_correct :
    HMapOk hmap_from_idx := HMapOk_halist T V.

  Definition interp_st
    : itree (STEvent T S V +' E) ~> stateT M (itree (E)) :=
    interp_state handle_STEvent_leave_rest.

  
End Translation.

Definition runST {A : Type}
  {T S : Type} {ltu : T -> T -> Prop}
  `{Ix T ltu}
  `{Ix_Correct T}
  `{EqDec T eq}
  `{STRefClass T}
  {E : Type -> Type}
  {V : T -> Type} `{exceptE Err -< E}
  (f : forall (S : Type), itree ((STEvent T S V) +' E) A)
  : itree E A :=
  fmap snd (interp_st ltu _ (f unit) HMap.empty).

(* CPP Bindings *)

Crane Extraction Implicit newSTRef[1].
Crane Extract Skip Ix_Correct.
Crane Extract Skip CmpDec_Correct.
Crane Extract Skip STEvent.
Crane Extract Skip CmpDec.
Crane Extract Skip max.
Crane Extract Skip mkSTRef.
Crane Extract Skip STRefToIx.
(* NOTE: skipping STRefClass seems to drop too much typing information,
 and the value types within references are not inferred. *)
(* Crane Extract Skip STRefClass. *)
Crane Extract Inlined Constant STRef => "%t2".
Crane Extract Inlined Constant newSTRef => "%result = %a1".
Crane Extract Inlined Constant readSTRef => "%a1".
Crane Extract Inlined Constant writeSTRef => "%a1 = %a2".
(* array extraction *)

Crane Extract Inductive STArray => "std::vector<%t2> *" [ "" ].
Crane Extract Inlined Constant newArray =>
"%result = new std::remove_pointer_t<decltype(%result)>(%a2 - %a1 + 1, %a3)".
Crane Extract Inlined Constant readArray => "(*%a1)[%a2]".
Crane Extract Inlined Constant writeArray => "(*%a1)[%a2] = %a3".

(* TODO: do we need remove_cvref_t below? *)
Crane Extract Inlined Constant newListArray =>
  "%result = new std::remove_pointer_t<decltype(%result)>(%a2 - %a1 + 1); { auto _xs = %a3; for (size_t _i = 0; _i < %result->size(); _i++) { if (std::holds_alternative<typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v())) { auto& [_a, _l] = std::get<typename std::remove_cvref_t<decltype(_xs)>::Cons>(_xs.v_mut()); (*%result)[_i] = _a; if (_l) _xs = *_l; } } }".
Crane Extract Inlined Constant getElems =>
  "[&]() { using _E = typename std::remove_pointer_t<std::remove_cvref_t<decltype(%a1)>>::value_type; List<_E> _r = List<_E>::nil(); for (size_t _i = %a1->size(); _i > 0; _i--) { _r = List<_E>::cons((*%a1)[_i - 1], std::move(_r)); } return _r; }()".

