(* SPDX-License-Identifier: BSD-3-Clause *)
From Stdlib Require Import Arith Relation_Definitions Relation_Operators Wellfounded.Lexicographic_Product.
From Crane.Libraries.ParseALot.Parser Require Import Tactics.


(** Lexicographic product of [lt] on [nat * nat], instantiating the stdlib [slexprod]. *)
Definition lex_nat_pair := slexprod nat nat lt lt.

(** [lex_nat_pair] is well-founded because [lt] on [nat] is well-founded and [slexprod] preserves well-foundedness. *)
Lemma lex_nat_pair_wf : well_founded lex_nat_pair.
Proof.
  apply wf_slexprod; apply lt_wf.
Defined.

(** Defines a lexicographic strict order on triples [(A * B * C)] and proves it well-founded when each component order is. *)
Section triple_lt.

    Variables (A B C : Type)
              (ltA : relation A) (ltB : relation B) (ltC : relation C).

    (** Lexicographic order on triples: a triple is smaller if its first differing component is smaller. *)
    Inductive triple_lex : A * B * C -> A * B * C -> Prop :=
    | triple_fst_lt :
        forall x x' y y' z z',
          ltA x x' -> triple_lex (x, y, z) (x', y', z')
    | triple_snd_lt :
        forall x y y' z z',
          ltB y y' -> triple_lex (x, y, z) (x, y', z')
    | triple_thd_lt :
        forall x y z z',
          ltC z z' -> triple_lex (x, y, z) (x, y, z').

    Hint Constructors triple_lex : core.

    (** [triple_lex] is well-founded whenever all three component orders are, proved by nested accessibility inductions. *)
    Lemma triple_lex_wf :
      well_founded ltA
      -> well_founded ltB
      -> well_founded ltC
      -> well_founded triple_lex.
    Proof.
      intros wfA wfB wfC [[x y] z].
      revert y z.
      induction (wfA x) as [x _ IHx].
      intros y.
      induction (wfB y) as [y _ IHy].
      intros z.
      induction (wfC z) as [z _ IHz].
      constructor.
      intros [[x' y'] z'] H.
      inv H; eauto.
    Defined.

End triple_lt.

(** Lexicographic order on [nat * nat * nat] triples, used as a concrete termination measure. *)
Definition lex_nat_triple := triple_lex nat nat nat lt lt lt.

(** [lex_nat_triple] is well-founded, following directly from [triple_lex_wf] and [lt_wf]. *)
Lemma lex_nat_triple_wf : well_founded lex_nat_triple.
Proof.
  apply triple_lex_wf; apply lt_wf.
Defined.
