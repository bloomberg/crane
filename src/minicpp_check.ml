(** A validator for the MiniCpp IR.

    Crane's erasure invariants — which values are physically inside a
    [std::any], and at what shape they may be read back out — are decided at
    many sites across {!Translation}, {!Gen_decls} and {!Loopify}, and were
    until now recorded only in comments.  When two of those sites disagree the
    symptom is a [std::bad_any_cast] in a test binary, arbitrarily far from the
    site that made the wrong choice.

    This module turns the comments into checks that run at a pass boundary.  It
    is deliberately conservative: it reports only situations that are wrong
    under {e any} reading of the surrounding code, so a report is a bug rather
    than a style note.

    Enabled by the [CRANE_CHECK_IR] environment variable:
    - unset or ["0"] — off, zero cost beyond one boolean test per declaration;
    - ["1"] — report each distinct violation once, as a warning;
    - ["strict"] — raise on the first violation.

    See [docs/nanopass-plan.md] for where this sits in the wider plan. *)

open Names
open Minicpp

(** How the checker reacts to a violation. *)
type mode =
  | Off
  | Warn  (** Report each distinct message once and keep going. *)
  | Strict  (** Raise on the first violation. *)

(** Read once: the environment does not change during extraction, and this is
    tested for every declaration printed. *)
let mode =
  lazy
    ( match Sys.getenv_opt "CRANE_CHECK_IR" with
    | None | Some "" | Some "0" -> Off
    | Some "strict" -> Strict
    | Some _ -> Warn )

(** Messages already reported, so that a violation replicated across every
    instantiation of a template is not printed hundreds of times. *)
let reported : (string, unit) Hashtbl.t = Hashtbl.create 16

(** [violation where what] reports a broken invariant detected while [where]
    (a pass name, for orientation) was the most recent thing to run. *)
let violation where what =
  let msg = Printf.sprintf "IR check (%s): %s" where what in
  match Lazy.force mode with
  | Off -> ()
  | Strict -> CErrors.user_err (Pp.str msg)
  | Warn ->
    if not (Hashtbl.mem reported msg) then begin
      Hashtbl.replace reported msg ();
      (* Straight to stderr rather than through {!Feedback}: the [coq.theory]
         dune rule does not surface Rocq warnings, and a check nobody sees is
         worse than no check. *)
      prerr_endline msg;
      flush stderr
    end

(** A short, structural rendering of a type.  The real pretty-printer lives in
    {!Cpp_print}, which sits above this module, so the checker spells types
    itself rather than inverting the dependency for the sake of a diagnostic. *)
let rec show_ty = function
  | Tany -> "std::any"
  | Topaque -> "opaque"
  | Tvoid -> "void"
  | Tglob (g, args, _) -> show_app (Common.pp_global_name Common.Type g) args
  | Tid (id, args) -> show_app (Id.to_string id) args
  | Tid_external (id, args) -> show_app (Id.to_string id) args
  | Tvar (i, _) -> Printf.sprintf "_T%d" i
  | Tshared_ptr t -> "shared_ptr<" ^ show_ty t ^ ">"
  | Tref t -> show_ty t ^ "&"
  | Tptr t -> show_ty t ^ "*"
  | Tmod (_, t) | Tnamespace (_, t) -> show_ty t
  | Tqualified (t, id) -> show_ty t ^ "::" ^ Id.to_string id
  | Tapply (t, args) -> show_app (show_ty t) args
  | Tfun (dom, cod) ->
    Printf.sprintf "(%s) -> %s" (String.concat ", " (List.map show_ty dom))
      (show_ty cod)
  | t -> if Ml_type_util.is_cpp_dummy_type t then "std::any" else "_"

and show_app head = function
  | [] -> head
  | args -> head ^ "<" ^ String.concat ", " (List.map show_ty args) ^ ">"

(** {2 The invariants} *)

(** [is_box e] — [e] constructs a [std::any] around a value.  Translation
    spells boxing as a converting constructor at the erased type. *)
let is_box = function
  | CPPconverting_ctor (ty, [_]) -> Ml_type_util.prints_as_any ty
  | _ -> false

(** [check_expr where e] tests the expression-level invariants at [e] itself.
    Recursion is the caller's job. *)
let check_expr where e =
  match e with
  (* [any_cast<std::any>] does not unwrap the box: it asks whether the box
     holds a *further* [std::any], and throws when it does not.  Whatever the
     producer meant, this is not it. *)
  | CPPany_cast (ty, _) when Ml_type_util.prints_as_any ty ->
    violation where
      (Printf.sprintf "any_cast to an erased type (%s) never unwraps a box"
         (show_ty ty))
  (* Two sites each believed they owned the boundary: one boxed, the other
     boxed the result.  The inner value is then unreachable, because the
     consumer casts once. *)
  | CPPconverting_ctor (ty, [inner])
    when Ml_type_util.prints_as_any ty && is_box inner ->
    violation where "a box built around a box"
  (* Dead work, and the same double-ownership smell: the value is boxed only
     to be immediately read back out. *)
  | CPPany_cast (_, inner) when is_box inner ->
    violation where "an any_cast applied directly to a freshly-built box"
  | _ -> ()

(** {2 Traversal} *)

let rec walk_stmts where stmts = List.iter (walk_stmt where) stmts

and walk_stmt where s =
  iter_stmt_children ~on_expr:(walk_expr where) ~on_stmts:(walk_stmts where) s

and walk_expr where e =
  check_expr where e;
  iter_expr_children ~on_expr:(walk_expr where) ~on_stmts:(walk_stmts where) e

let rec walk_field where (f, _, _) =
  match f with
  | Ffundef (_, _, _, body) -> walk_stmts where body
  | Fmethod m -> walk_stmts where m.mf_body
  | Fconstructor (_, inits, _, _) ->
    List.iter (fun (_, e) -> walk_expr where e) inits
  | Ftemplate_ctor (_, _, _, body) -> walk_stmts where body
  | Fdestructor body -> walk_stmts where body
  | Fnested_struct (_, fields) -> List.iter (walk_field where) fields
  | Fvar _ | Fvar' _ | Ffundecl _ | Fnested_using _ | Fdeleted_ctor
  | Fdefaulted_special_members -> ()

let rec walk_decl where d =
  match d with
  | Dtemplate (_, constr, inner) ->
    Option.iter (walk_expr where) constr;
    walk_decl where inner
  | Dnspace (_, decls) -> List.iter (walk_decl where) decls
  | Dfundef (_, _, _, body, _) -> walk_stmts where body
  | Dfundecl _ -> ()
  | Dstruct s ->
    Option.iter (walk_expr where) s.ds_constraint;
    List.iter (walk_field where) s.ds_fields
  | Dasgn (_, _, e) -> walk_expr where e
  | Dconcept (_, e) -> walk_expr where e
  | Dstatic_assert (e, _) -> walk_expr where e
  | Dusing _ -> ()
  | Denum _ -> ()

(** [check ~where decl] validates [decl] against the invariants above.  A no-op
    unless [CRANE_CHECK_IR] is set; [where] names the pass that last touched
    the declaration, so a report points at the pass to look in. *)
let check ~where (decl : cpp_decl) : unit =
  if Lazy.force mode <> Off then walk_decl where decl
