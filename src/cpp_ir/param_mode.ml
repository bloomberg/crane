(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a parameter is passed ({!Grammar.Param_mode}): its ownership, the
    physical form it is declared in, and what it is to its body.  The
    decision is made once, where the parameter is generated, and recorded
    beside the declaration ({!Grammar.Function}, {!Grammar.Method},
    {!Grammar.Lambda}) and in the callable's plan; the declared type is its
    spelling.  Under [CRANE_CHECK_IR] the two are checked to agree
    ({!disagreement}). *)

include Grammar.Param_mode

let make ?(role = Value) ownership form = {ownership; form; role; invalidates_views = false}

(** Owned, by value: the caller moves or copies its argument in. *)
let owned = make Owned By_value

(** Borrowed, lent by const reference. *)
let lent = make Borrowed By_const_reference

(** Borrowed, but copied: a value no reference is worth taking to. *)
let copied = make Borrowed By_value

(** Borrowed, copied into a [const] value: a lifted helper's. *)
let const_copied = make Borrowed By_const_value

(** A callable the head deduces, by forwarding reference. *)
let forwarded = make Forwarded By_forwarding_reference

(** The receiver a loop over a method is entered with: a pointer to the
    object, by value. *)
let receiver = make ~role:Receiver Borrowed By_value

let equal (a : t) (b : t) = a = b

(** The type a parameter whose value is of type [t] is declared at when
    passed in [form]; for a view, [t] is the view type already. *)
let declare form (t : 'p Type.t) : 'p Type.t =
  match form with
  | By_value | By_view _ -> t
  | By_const_value -> Const t
  | By_const_reference -> Reference (Lvalue, Const t)
  | By_forwarding_reference -> Reference (Forwarding, t)
  | By_reference -> Reference (Lvalue, t)

(** The form the declared type [t] spells. *)
let rec spelled_form : 'p Type.t -> form = function
  | In_namespace (_, t) -> spelled_form t
  | Reference (Lvalue, Const _) -> By_const_reference
  | Reference (Lvalue, _) -> By_reference
  | Reference (Forwarding, _) -> By_forwarding_reference
  | Const _ -> By_const_value
  | _ -> By_value

(** The mode the declared type [t] spells, owned where [owned] says: for a
    parameter whose mode was recorded nowhere, which under [CRANE_CHECK_IR]
    is a violation where a mode is read, and for a local, whose declaration
    is its only record. *)
let spelled ?(owned = false) (t : 'p Type.t) =
  match spelled_form t with
  | By_forwarding_reference -> forwarded
  | By_value -> if owned then make Owned By_value else copied
  | form -> make Borrowed form

(** Whether the body holds a value of its own, which it may move from: one
    declared by value, not [const], a reference or the receiver. *)
let holds_own_value m = m.form = By_value && m.role = Value

(** The view a parameter is, if it is one. *)
let view m = match m.form with By_view (k, head) -> Some (k, head) | _ -> None

(** Whether the parameter is declared by value, [const] or not, a pointer
    the receiver is included. *)
let by_value m = m.form = By_value

(** Whether the parameter names what it holds [const]: by [const] value, or
    by [const] reference. *)
let const_qualified m = match m.form with By_const_value | By_const_reference -> true | _ -> false

(** Whether the parameter is the receiver. *)
let is_receiver m = m.role = Receiver

(** The type of the value a parameter in mode [m] declared at [t] stands
    for: [t] without the declarator [m]'s form adds ({!declare}). *)
let rec value_type m (t : 'p Type.t) : 'p Type.t =
  match (m.form, t) with
  | (By_value | By_view _), t -> t
  | By_const_value, Const t -> t
  | By_const_reference, Reference (Lvalue, Const t) -> t
  | (By_forwarding_reference | By_reference), Reference (_, t) -> t
  | _, In_namespace (_, t') when spelled_form t' = m.form -> value_type m t'
  | _, t -> t

(** What is wrong of the mode [m] recorded of a parameter declared at [t],
    if anything: a form the type does not spell, an ownership the form
    cannot have, or a receiver not declared as a pointer. *)
let disagreement m (t : 'p Type.t) =
  let name = function
    | By_value -> "by value"
    | By_const_value -> "by const value"
    | By_const_reference -> "by const reference"
    | By_forwarding_reference -> "by forwarding reference"
    | By_reference -> "by reference"
    | By_view (Read_view, _) -> "by read view"
    | By_view (Write_view, _) -> "by writable view"
  in
  let spelled = spelled_form t in
  (* A view is a value, spelled as one. *)
  let recorded = match m.form with By_view _ -> By_value | f -> f in
  if spelled <> recorded then Some ("recorded " ^ name m.form ^ ", declared " ^ name spelled)
  else
    match (m.ownership, m.form) with
    | Owned, (By_const_value | By_const_reference | By_forwarding_reference | By_reference | By_view _) ->
      Some ("recorded owned " ^ name m.form)
    | Forwarded, (By_value | By_const_value | By_const_reference | By_reference | By_view _)
     |Borrowed, By_forwarding_reference ->
      Some "recorded forwarded other than by forwarding reference"
    | _ -> (
      match (m.role, t) with
      | Receiver, Pointer _ -> None
      | Receiver, _ -> Some "recorded the receiver, declared other than a pointer"
      (* A value may be a pointer: a typed mapping's canonical type can be
         one (a raw-pointer handle). *)
      | Value, _ -> None )
