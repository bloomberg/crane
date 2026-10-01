From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** A polymorphic mutual traversal in the shape of Vellvm's
    [Traversal.ft_exp] / [ft_metadata]: a class parameter ([Endo]), a function
    parameter [f], a local closure over the recursion ([ftpair]), and the
    mutual partner partially applied under [map] ([map (ft_md U V f) l]).
    With [Set Crane Loopify] the generated loop binds a non-const lvalue
    reference to a moved temporary ("non-const lvalue reference to type
    '(lambda ...)' cannot bind to a temporary") and calls [ft_e] with
    arguments it has no overload for.

    [loopify_mutual_result_types] (fixed in a9df8ed7e) is the same pair
    without the parameters; this is what is left of Vellvm's global
    [Set Crane Loopify] on 19ffa36ec: all 4 of its remaining errors. *)

Module LoopifyMutualPartialApp.

  Class Endo (T : Type) := endo : T -> T.

  Inductive e (U : Type) := Leaf (n : nat) | Tag (u : U) | Add (a b : e U) | Meta (m : md U)
  with md (U : Type) := MNull | MConst (u : U) (x : e U) | MNode (l : list (md U)) | MPair (a b : md U).
  Arguments Leaf {U}. Arguments Tag {U}. Arguments Add {U}. Arguments Meta {U}.
  Arguments MNull {U}. Arguments MConst {U}. Arguments MNode {U}. Arguments MPair {U}.

  Fixpoint ft_e `{Endo nat} (U V : Type) (f : U -> V) (x : e U) : e V :=
    let ftpair (p : U * e U) := (f (fst p), ft_e U V f (snd p)) in
    match x with
    | Leaf n => Leaf (endo n)
    | Tag u => Tag (f u)
    | Add a b => Add (ft_e U V f a) (ft_e U V f b)
    | Meta m => Meta (ft_md U V f m)
    end
  with ft_md `{Endo nat} (U V : Type) (f : U -> V) (m : md U) : md V :=
    match m with
    | MNull => MNull
    | MConst u x => MConst (f u) (ft_e U V f x)
    | MNode l => MNode (map (ft_md U V f) l)
    | MPair a b => MPair (ft_md U V f a) (ft_md U V f b)
    end.

  Fixpoint sum_e (x : e nat) : nat :=
    match x with
    | Leaf n => n
    | Tag u => u
    | Add a b => sum_e a + sum_e b
    | Meta m => sum_md m
    end
  with sum_md (m : md nat) : nat :=
    match m with
    | MNull => 0
    | MConst u x => u + sum_e x
    | MNode l => fold_left (fun acc m => acc + sum_md m) l 0
    | MPair a b => sum_md a + sum_md b
    end.

  #[export] Instance endo_double : Endo nat := fun n => 2 * n.

  Definition sample : e nat :=
    Add (Leaf 1) (Meta (MPair (MConst 5 (Add (Leaf 2) (Tag 7))) (MNode [MNull; MConst 1 (Leaf 4)]))).

  (** leaves doubled: 2*(1+2+4) = 14; tags and consts +100 each: 107 + 105 + 101 = 313 *)
  Definition check (_ : unit) : bool :=
    Nat.eqb (sum_e (ft_e nat nat (fun u => u + 100) sample)) (14 + 313).

End LoopifyMutualPartialApp.

Set Crane Loopify.
Crane Extraction "loopify_mutual_partial_app" LoopifyMutualPartialApp.
