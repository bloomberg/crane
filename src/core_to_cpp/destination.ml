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
  | Assign of Names.Id.t * Slot_type.t  (** [x = e;], [x] declared before the statements *)
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

(** The slot of a type a position states, or [Free] where it states none. *)
let slot_of (t : Cpp_ir.Lowered.Type.t option) : Slot_type.t =
  match t with Some t -> Exactly t | None -> Free

(** A [return] from the function whose body is being lowered, at the result
    type lowering has for it. *)
let return_ cx = Return (slot_of (Lowering_state.current_cpp_return_type cx ()))

(** [Return] at [t], or [Return_void] where [t] is [void]. *)
let return_at (t : Cpp_ir.Lowered.Type.t option) =
  match t with Some Void -> Return_void | t -> Return (slot_of t)

(** The slot the value is put at. *)
let rec slot = function
  | Return s | Assign (_, s) -> s
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
  | Assign (x, _) -> Bind_variable (x, Existing, e)
  | Discard -> Expression e
  | Adapted (f, d) -> build d (f e)
  | Custom c -> c.build e

(** Under [CRANE_PROBE], whether the slot [d] states agrees with the
    ambient return type ({!Lowering_state.current_cpp_return_type}) at the
    tail: the two describe one position while both exist. *)
let check_ambient cx d =
  if Base.Probe.enabled () then
    match d with
    | Discard -> ()
    | _ ->
      let ambient = slot_of (Lowering_state.current_cpp_return_type cx ()) in
      Base.Probe.hit "dest-ambient" (fun () ->
          if slot d = ambient then "agree"
          else "disagree in " ^ Typed_checks.site cx)

(** The statement the typed value [x] becomes at [d], [x] checked against
    [d]'s slot ({!Typed_checks.fit}). *)
let finish cx d (x : Cpp_ir.Typed.t) : Cpp_ir.Lowered.Stmt.t =
  check_ambient cx d;
  Typed_checks.fit cx ~site:(if discards d then "discard" else "destination") x (slot d);
  let s = build d x.expr in
  (* A value returned is recorded for the join of the lambda returning it
     ({!Lowering_state.with_returns}): [x]'s type where [x] is what is
     returned, else what the node says. *)
  ( match (s, d) with
  | Return (Some e), Return _ -> Lowering_state.record_return cx e x.ty
  | Return (Some e), _ -> Lowering_state.record_return cx e (Cpp_ir.Typed.node_type e)
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
