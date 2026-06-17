(** WIP test: bad_any_cast in parser semantic actions.
    Reproduces the crash in parse-a-lot where Crane-generated code uses
    any_cast on type-erased semantic values built from dependent pairs.

    The pattern: a type family [sem_ty : tag -> Type] is erased to std::any.
    Grammar entries use [sigT] to pair productions with semantic actions whose
    types depend on the production. Crane wraps these in std::any but the
    cast targets don't match at runtime. *)
From Stdlib Require Import List String.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Require Crane.Extraction.

Module ParserAnyCast.

(** A tag type with different semantic types per variant *)
Inductive tag := A | B.

Definition sem_ty (t : tag) : Type :=
  match t with
  | A => nat
  | B => string
  end.

(** A grammar entry: dependent pair of tag and its semantic value *)
Definition entry := { t : tag & sem_ty t }.

(** Construct entries *)
Definition entry_a : entry := existT _ A 42.
Definition entry_b : entry := existT _ B "hello"%string.

(** A function that examines entries via projT1/projT2 — requires correct any_cast *)
Definition get_tag (e : entry) : tag := projT1 e.

Definition process_entries (es : list entry) : list tag :=
  map get_tag es.

Definition test_entries : list entry := [entry_a; entry_b].
Definition test_result : list tag := process_entries test_entries.

(** More importantly: a function that uses the dependent second projection,
    which requires correct type-erased casting *)
Definition get_a_value (e : entry) : nat :=
  match e with
  | existT _ A n => n
  | existT _ B _ => 0
  end.

Definition sum_a_entries (es : list entry) : nat :=
  fold_left (fun acc e => acc + get_a_value e) es 0.

Definition test_sum : nat := sum_a_entries test_entries.

(** Second bug: when a non-uniform type family is erased to std::any,
    Crane generates any_cast<std::any>(value) for branches that return unit.
    This crashes because monostate is stored, not std::any.
    Reproduces defLiteral in parse-a-lot's Semantic module. *)

Inductive label := NumL | StrL | UnitL.

(** Non-uniform type family: different types per branch -> erased to std::any *)
Definition label_sem (l : label) : Type :=
  match l with
  | NumL => nat
  | StrL => string
  | UnitL => unit
  end.

Definition def_label : label := UnitL.

(** This is the problematic definition: it has type [label_sem UnitL = unit]
    and the value [tt]. Crane will generate any_cast<std::any>(monostate). *)
Definition def_literal : label_sem def_label := tt.

(** A sigT entry using label_sem — forces actual use of the erased type *)
Definition labeled_entry := { l : label & label_sem l }.

Definition make_default_entry : labeled_entry :=
  existT _ def_label def_literal.

Definition get_entry_label (e : labeled_entry) : label := projT1 e.

Definition test_default_label : label := get_entry_label make_default_entry.

End ParserAnyCast.

Set Crane Loopify.
Crane Separate Extraction
  ParserAnyCast.test_result
  ParserAnyCast.test_sum
  ParserAnyCast.test_default_label.
