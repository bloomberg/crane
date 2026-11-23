(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Where the value statements compute goes ({!Stmts.gen_stmts}): returned,
    assigned to a variable declared before them, discarded, or handed to a
    statement a caller builds.  Each destination states its slot, the type
    the value is put at, so a tail and a let's right-hand side meet a real
    {!Cpp_ir.Lowered.Slot_type.t} rather than the enclosing function's
    return type; and whether it returns, which lowering used to find out by
    calling a continuation on a dummy value. *)

module Slot_type = Cpp_ir.Lowered.Slot_type

type t =
  | Return of Slot_type.t  (** [return e;], from a function whose result is the slot *)
  | Return_void
      (** [e; return;] from a function returning [void]; a value without
          effects ({!Cpp_build.return_into_void}) is dropped *)
  | Assign of {
      var : Names.Id.t;
      into : Slot_type.t;
      assigned : Cpp_ir.Typed.t list ref;
    }
      (** [var = e;], [var] declared before the statements; each value
          assigned is recorded in [assigned] ({!assign}, {!assigned}) *)
  | Discard  (** [e;], the value unused *)
  | Adapted of (Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Expr.t) * t
      (** the value rewritten (unboxed) before it goes to the inner destination *)
  | Custom of {
      build : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t;
      into : Slot_type.t;
      returns : bool;
    }
      (** a statement the caller builds around the value at [into]
          (a suspension, a reified [ret]); [returns] says whether it is a
          [return] *)

(** An assignment to [x] at [into], recording nothing yet. *)
let assign x into = Assign {var = x; into; assigned = ref []}

(** The assignment of a let's right-hand side to its binder [x], bound
    at the Core type [t].  Where a position in the right-hand side states
    nothing it falls back to this slot's type
    ({!Coerce.position_cpp_ty}): the bound value is not the enclosing
    function's result, so it is the binder's own type, its erased parts
    spelled erased, where this scope can write it, and otherwise nothing.
    Never the enclosing function's result: a value bound in its body has a
    type of its own, and spelled at the result's it is a [List<pair<...>>]
    holding [Sum]s.  A binder erasure took the whole type from --
    [nt_semty x], a type computed from a value -- holds a box, and its
    value is one. *)
let bind_let cx env x t =
  let c = Types.cpp_of_core cx env t in
  assign x (if Cpp_ir.Types.prints_as_any c then Exactly c else match Types.spell_in_scope cx c with Some c -> Exactly c | None -> Free)

(** The type [d]'s slot states, if it states one. *)
let rec stated = function
  | Return (Exactly t) | Assign {into = Exactly t; _} -> Some t
  | Return_void -> Some Cpp_ir.Type.Void
  | Adapted (_, d) -> stated d
  | Custom {into = Exactly t; _} -> Some t
  | Return _ | Assign _ | Custom _ | Discard -> None

(** The typed value [d] assigned as [e] (the node itself, not an equal
    one): what lowering synthesised for the value an assignment the
    statements end in carries. *)
let rec assigned d (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Typed.t option =
  match d with
  | Assign a -> List.find_opt (fun (x : Cpp_ir.Typed.t) -> x.expr == e) !(a.assigned)
  | Adapted (_, d) -> assigned d e
  | Return _ | Return_void | Discard | Custom _ -> None

(** The slot of a type a position states, or [Free] where it states none. *)
let slot_of (t : Cpp_ir.Lowered.Type.t option) : Slot_type.t =
  match t with Some t -> Exactly t | None -> Free

(** The slot of a function's result: the type it states, or where it
    states none, the join of what it returns (C++ deduces it). *)
let result_slot (t : Cpp_ir.Lowered.Type.t option) : Slot_type.t =
  match t with Some t -> Exactly t | None -> Join

(** A [return] from the function whose body is being lowered, its result
    type [ret]. *)
let return_ ~ret = Return (result_slot ret)

(** [Return] at [t], or [Return_void] where [t] is [void]. *)
let return_at (t : Cpp_ir.Lowered.Type.t option) =
  match t with Some Void -> Return_void | t -> Return (result_slot t)

(** The slot the value is put at. *)
let rec slot = function
  | Return s | Assign {into = s; _} -> s
  | Return_void -> Exactly Void
  | Discard -> Free
  | Adapted (_, d) -> slot d
  | Custom c -> c.into

(** Whether the statement the value becomes is a [return]. *)
let rec returns = function
  | Return _ | Return_void -> true
  | Assign _ | Discard -> false
  | Adapted (_, d) -> returns d
  | Custom c -> c.returns

(** Whether the value is discarded. *)
let rec discards = function
  | Discard -> true
  | Adapted (_, d) -> discards d
  | Return _ | Return_void | Assign _ | Custom _ -> false

(** [d] with the value first rewritten by [f]. *)
let adapted f d = Adapted (f, d)

(** The statement [e] becomes at [d]. *)
let rec build d (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Stmt.t =
  match d with
  | Return _ -> Return (Some e)
  | Return_void -> Cpp_build.return_into_void e
  | Assign {var; _} -> Bind_variable (var, Existing, e)
  | Discard -> Expression e
  | Adapted (f, d) -> build d (f e)
  | Custom c -> c.build e

(** Record [x] as assigned by [d]'s innermost assignment, if any. *)
let rec record_assigned d (x : Cpp_ir.Typed.t) =
  match d with
  | Assign a -> a.assigned := x :: !(a.assigned)
  | Adapted (_, d) -> record_assigned d x
  | Return _ | Return_void | Discard | Custom _ -> ()

(** The statement the typed value [x] becomes at [d], [x] checked against
    [d]'s slot ({!Typed_checks.fit}). *)
let finish cx d (x : Cpp_ir.Typed.t) : Cpp_ir.Lowered.Stmt.t =
  Typed_checks.fit cx ~site:(if discards d then "discard" else "destination") x (slot d);
  let s = build d x.expr in
  (* A value returned is recorded for the join of the lambda returning it
     ({!Lowering_state.with_returns}): [x]'s type where [x] is what is
     returned, else what the node says. *)
  ( match (s, d) with
  | Return (Some e), Return _ -> Lowering_state.record_return cx e x.ty
  | Return (Some e), _ -> Lowering_state.record_return cx e (Cpp_ir.Typed.node_type e)
  | Bind_variable (_, Existing, e), _ -> record_assigned d (if e == x.expr then x else Cpp_ir.Typed.of_node e)
  | _ -> () );
  s

(** [finish] of [x], where [x] is an immediately invoked lambda inlined
    where [d] returns: its returns become [d]'s statements
    ({!Cpp_build.inline_returns}).  An invoked lambda is rebuilt as one
    that runs in place. *)
let finish_inlined cx d (x : Cpp_ir.Typed.t) : Cpp_ir.Lowered.Stmt.t list =
  match x.expr with
  | Call (_, Lambda {params = []; return_type; body; _}, []) when body <> [] -> (
    let rebuilt () = [finish cx d (Cpp_ir.Typed.rewrap (fun _ -> Cpp_ir.Build.iife return_type body) x)] in
    if not (returns d) then rebuilt ()
    else
      (* Each return is the lambda's value, at the type it was returned at
         where its body recorded one, else at the type C++ gives it where
         its node does not say. *)
      let returned v =
        match Lowering_state.returned_type cx v with
        | Some ty -> Cpp_ir.Typed.v ~ty v
        | None -> Cpp_ir.Typed.or_type x.ty (Cpp_ir.Typed.of_node v)
      in
      match Cpp_build.inline_returns (fun v -> finish cx d (returned v)) body with
      | Some stmts -> stmts
      | None -> rebuilt () )
  | _ -> [finish cx d x]
