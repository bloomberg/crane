(* Under the reified ITree mapping, a computation whose type names the monad
   through an alias is still a tree.

   [stateT S (itree E) T] is [S -> itree E (S * T)], so [twice] below runs in
   [itree]: its [ITree.bind] builds a tree.  The mode a declaration is
   generated in was read off the codomain's spelling, [stateT], which is no
   monad, so [twice] was generated sequentially and its bind became a
   statement binding the tree as if it were the pair inside it:

     std::pair<uint64_t, uint64_t> p = c(s);

     error: no viable conversion from 'std::shared_ptr<ITree<...>>' to
            'std::pair<uint64_t, uint64_t>'

   Once the mode is right, the bind's first argument [c s] -- a parameter
   of alias type applied to the state -- must be recognised as a tree, not
   wrapped in [ITree<...>::ret]; likewise [m] and [seed] below, whose
   types spell [itree] through the non-arrow alias [M], and the binds of
   the constant [from_seed], whose generation never set the mode at all.

   Reduced from wip/handler_lambda_targ_undeclared ([on_ls]). *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITreeReified.
From ITree Require Import ITree.
Import ITree.Basics.Basics.Monads.

Module StateTAliasReified.
  Definition tick : stateT nat (itree void1) nat := fun s => Ret (S s, s).

  Definition twice (c : stateT nat (itree void1) nat) : stateT nat (itree void1) nat :=
    fun s => ITree.bind (c s) (fun p =>
             ITree.bind (c (fst p)) (fun q => Ret (fst q, snd p + snd q))).

  Definition run (n : nat) : itree void1 (nat * nat) := twice tick n.

  Definition M := itree void1.

  Definition seed : M nat := Ret 7.

  Definition plus_one (m : M nat) : M nat := ITree.bind m (fun x => Ret (S x)).

  Definition from_seed : M nat := ITree.bind seed (fun x => plus_one (Ret x)).

  Definition seeded (n : nat) : M nat := ITree.bind seed (fun x => plus_one (Ret (x + n))).
End StateTAliasReified.

Crane Extraction "state_t_alias_reified" StateTAliasReified.
