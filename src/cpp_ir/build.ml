(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Building CppIR the way declaration generation writes it: the calls,
    type variables and member shapes generators make, each stated once. *)

open Grammar

(** [signature ?yields ?params ~nargs ()] is what a builder knows about a
    call of [nargs] arguments.  [params] is recorded only when it is aligned
    with the arguments; a length mismatch is no knowledge at all, so it is
    dropped rather than stored misaligned. *)
let signature ?yields ?params ~nargs () : 'p Call.signature =
  { yields = (match yields with Some t -> Yields t | None -> Untyped);
    params = (match params with Some ts when List.length ts = nargs -> Types ts | _ -> Unknown);
    constructs = None;
    occurrence = None }

(** [call ?yields ?params fn args] is a call of [fn] on [args], in source
    order.  Omitting [yields] or [params] is a claim -- that the callee has
    no Crane-level type there.  A call of an abort with no arguments is the
    abort, which already carries the type the call would have had. *)
let call ?yields ?params (fn : 'p Expr.t) (args : 'p Expr.t list) : 'p Expr.t =
  match (fn, args) with
  | Abort _, [] -> fn
  | _ -> Call (signature ?yields ?params ~nargs:(List.length args) (), fn, args)

(** [named_variable x] is the type variable known only by its name [x]. *)
let named_variable x : 'p Type.t = Variable (Named x)

(** [typenames xs] declares each of [xs] a plain [typename] parameter. *)
let typenames xs : 'p Template.parameters = List.map (fun x -> (Parameter_kind.Typename, x)) xs
