(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Edge cases for unit→void extraction. *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module UnitVoidEdge.

(* --- 1. Let-binding the result of a void-ified function --- *)
(* return_unit is void in C++. Binding its result in a let must not
   produce "void x = return_unit(5);" *)
Definition return_unit (n : nat) : unit := tt.

Definition let_bind_void_call : nat :=
  let x := return_unit 5 in
  match x with tt => 42 end.

(* --- 2. Recursive function returning unit --- *)
Fixpoint count_down (n : nat) : unit :=
  match n with
  | O => tt
  | S n' => count_down n'
  end.

(* --- 3. Higher-order: taking and forwarding a unit-returning callback --- *)
Definition apply_unit_fn (f : nat -> unit) (n : nat) : unit := f n.

(* --- 4. Higher-order: returning tt from a callback passed to a HOF --- *)
Definition map_to_unit (f : nat -> unit) (n : nat) : nat :=
  let _ := f n in 42.

(* --- 5. Polymorphic identity applied at unit --- *)
Definition id {A : Type} (x : A) : A := x.

(* id instantiated at unit in return position *)
Definition id_unit : unit := id tt.

(* id instantiated at unit in function return *)
Definition id_unit_fn (n : nat) : unit := id tt.

(* --- 6. Nested let-bindings with unit --- *)
Definition nested_lets : nat :=
  let a := return_unit 1 in
  let b := return_unit 2 in
  let c := return_unit 3 in
  42.

(* --- 7. Unit in option (should NOT void-ify) --- *)
Definition unit_some : option unit := Some tt.
Definition unit_none : option unit := None.

Definition match_option_unit (o : option unit) : nat :=
  match o with
  | Some _ => 1
  | None => 0
  end.

(* --- 8. Function returning option unit (NOT void) --- *)
Definition return_some_tt (n : nat) : option unit :=
  if Nat.eqb n 0 then None else Some tt.

(* --- 9. Unit-to-unit with intermediate computation --- *)
Definition unit_chain (u : unit) : unit :=
  let x := u in
  let y := x in
  y.

(* --- 10. Mutual style: one returns unit, other returns nat --- *)
(* Not using actual mutual recursion since that's complex, but
   simulating the pattern *)
Definition helper_void (n : nat) : unit := tt.
Definition use_helper (n : nat) : nat :=
  let _ := helper_void n in
  n.

(* --- 11. Match on unit in non-tail position --- *)
Definition match_unit_nontail (u : unit) : nat :=
  let x := match u with tt => 7 end in
  x.

(* --- 12. Function taking unit AND returning unit --- *)
Definition unit_to_unit_with_work (u : unit) : unit :=
  match u with
  | tt => tt
  end.

(* --- 13. Multiple unit-returning functions composed --- *)
Definition seq_voids (n : nat) : unit :=
  let _ := return_unit n in
  let _ := return_unit (S n) in
  tt.

(* --- 14. Bool-guarded unit return --- *)
Definition conditional_unit (b : bool) : unit :=
  if b then tt else tt.

(* --- 15. Unit value passed to polymorphic function --- *)
Definition poly_take {A : Type} (x : A) : nat := 42.
Definition take_tt : nat := poly_take tt.

(* --- 16. list unit (unit in structural position, should stay Unit) --- *)
Definition unit_list : list unit := cons tt (cons tt nil).

(* --- 17. Nested match on unit (both should be eliminated) --- *)
Definition double_match_unit (u1 u2 : unit) : nat :=
  match u1 with
  | tt => match u2 with
          | tt => 99
          end
  end.

(* === 18. (A -> unit) -> unit : HOF that takes AND returns unit === *)
Definition apply_and_discard (f : nat -> unit) (n : nat) : unit := f n.

(* Call it: both the callback and the outer function should be void *)
Definition test_apply_discard : unit := apply_and_discard return_unit 42.

(* === 19. Record with a unit field === *)
Record tagged_nat := mk_tagged {
  tn_value : nat;
  tn_tag   : unit;
}.

Definition make_tagged (n : nat) : tagged_nat :=
  mk_tagged n tt.

Definition get_value (t : tagged_nat) : nat := tn_value t.

Definition test_record_unit : nat :=
  let t := make_tagged 99 in
  get_value t.

(* === 20. Nested callback: returns a (unit -> unit) callback === *)
Definition make_callback (n : nat) : unit -> unit :=
  fun _ => return_unit n.

Definition test_make_callback : unit :=
  let f := make_callback 5 in
  f tt.

(* === 21. (A -> unit) -> (B -> unit) -> unit : multiple unit callbacks === *)
Definition multi_void_callbacks
  (f : nat -> unit) (g : bool -> unit) (n : nat) (b : bool) : unit :=
  let _ := f n in
  let _ := g b in
  tt.

Definition dummy_bool_void (_ : bool) : unit := tt.
Definition test_multi_cb : unit :=
  multi_void_callbacks return_unit dummy_bool_void 7 true.

(* Test values to verify correctness at runtime *)
Definition test_let_bind := let_bind_void_call.
Definition test_count_down := count_down 10.
Definition test_apply := apply_unit_fn return_unit 5.
Definition test_map := map_to_unit return_unit 5.
Definition test_nested := nested_lets.
Definition test_match_some := match_option_unit unit_some.
Definition test_match_none := match_option_unit unit_none.
Definition test_return_some := return_some_tt 1.
Definition test_use_helper := use_helper 7.
Definition test_match_nontail := match_unit_nontail tt.
Definition test_double_match := double_match_unit tt tt.
Definition test_take_tt := take_tt.

End UnitVoidEdge.

Crane Extraction "unit_void_edge" UnitVoidEdge.
