(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* A call as Core elaborates it, from the callee's type, the call's arguments
   and the lexical environment they are typed in alone: no C++ type is
   chosen, no expression generated, and no translation state is read. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "elaborated_call: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let nat = Tglob (r "nat", [], [])

let declare s ty =
  Table.add_type (r s) ty;
  MLglob (Global_use.monomorphic (r s))

let binder ?(role = Lexenv.Value) s ty = {Lexenv.eb_id = Id.of_string s; eb_type = ty; eb_role = role}

let elaborate ?(lex = Lexenv.empty) f args =
  Core_elaborate.elaborate_arguments ~lex (Global_use.monomorphic f) args

let () =
  let a = declare "a" nat and b = declare "b" nat and c = declare "c" nat in
  let f = r "f" in
  Table.add_type f (Tarr (nat, Tarr (nat, nat)));
  let exact = elaborate f [a; b] in
  check "a call at the callee's arity passes every argument"
    (exact.primary = [a; b] && exact.excess = [] && exact.regular = [a; b]);
  check "each argument has its role" (exact.roles = [Elaborated_call.Regular; Regular]);
  check "no dictionary, so none occupies a parameter"
    (exact.instances = [] && Elaborated_call.leading_params exact = 0);
  check "elaborating a call twice elaborates it alike"
    (Elaborated_call.same_roles exact (elaborate f [a; b]));
  let over = elaborate f [a; b; c] in
  check "an argument past the arity is applied to the result"
    (over.primary = [a; b] && over.excess = [c]
    && over.roles = [Elaborated_call.Regular; Regular; Excess]);
  let partial = elaborate f [a] in
  check "a partial application passes what it has" (partial.primary = [a] && partial.excess = []);
  let g = r "g" in
  Table.add_type g (Tarr (nat, Tarr (Tdummy Ktype, Tarr (nat, nat))));
  let eta = elaborate g [a; MLdummy Ktype; b] in
  check "a dummy at an erased domain is not a value argument"
    (eta.primary = [a; b] && eta.excess = []
    && eta.roles = [Elaborated_call.Regular; Dropped; Regular]);
  check "the callee's declared type is kept" (eta.callee_type = Table.find_type g)

(* A variable argument is a dictionary by the role its binder was bound
   with, not by its name: a declaration's class-typed parameter is one, a
   class-typed binder inside the body is a value. *)
let () =
  let kn = MutInd.make1 (KerName.make (ModPath.MPfile (DirPath.make [Id.of_string "T"])) (Label.make "C")) in
  Table.add_inductive_kind kn (TypeClass []);
  let class_ty = Tglob (GlobRef.IndRef (kn, 0), [], []) in
  let h = r "h" in
  Table.add_type h (Tarr (class_ty, Tarr (nat, nat)));
  let lex = Lexenv.push [binder "x" nat; binder ~role:Lexenv.Dictionary "inst" class_ty] Lexenv.empty in
  let call = elaborate ~lex h [MLrel 2; MLrel 1] in
  check "a declaration's class-typed parameter is passed as its dictionary"
    (call.instances = [MLrel 2] && call.regular = [MLrel 1]
    && call.roles = [Elaborated_call.Dictionary; Regular]);
  check "the dictionary occupies the leading parameter" (Elaborated_call.leading_params call = 1);
  let lex = Lexenv.push [binder "inst" class_ty; binder "x" nat] Lexenv.empty in
  let local = elaborate ~lex h [MLrel 1; MLrel 2] in
  check "a class-typed binder bound in a body is a value" (local.instances = [])

(* A call is found among the ones planned from Core by its use's occurrence,
   which survives the annotation rewrites a body goes through before it is
   translated: a polymorphic use is rebuilt by every rewrite of its types. *)
let () =
  let f = r "pf" in
  Table.add_type f (Tarr (Tvar (Schematic, 1), Tvar (Schematic, 1)));
  let scheme = Scheme.Id.fresh f ~arity:1 in
  let at_nat () =
    Global_use.polymorphic f
      (Scheme.Instantiation.make scheme (fun _ ->
           {Scheme.solution = Scheme.Type nat; source = Scheme.Not_written} ) )
  in
  let use = at_nat () in
  let rewritten = Global_use.map_types Fun.id use in
  check "a rewrite of a use's types keeps its occurrence"
    (Occurrence.equal (Global_use.occurrence use) (Global_use.occurrence rewritten));
  let again = at_nat () in
  check "a use built afresh is another occurrence"
    (not (Occurrence.equal (Global_use.occurrence use) (Global_use.occurrence again)));
  check "occurrences do not tell terms apart structurally" (MLglob use = MLglob again);
  let a = declare "pa" nat in
  let unit = ModPath.MPfile (DirPath.make [Id.of_string "U"]) in
  let elaborated =
    Core_elaborate.structure
      [(unit, [(Label.make "d", SEdecl (Dterm (r "d", MLapp (MLglob use, [a]), nat)))])]
  in
  (* The walk's result is a value: what it planned is read off it, with
     nothing installed. *)
  check "a call's roles are read off the elaboration, found by its rewritten use"
    (Core_elaborate.roles elaborated rewritten 1 = Some [Elaborated_call.Regular]);
  check "an application the walk did not see has no roles there"
    (Core_elaborate.roles elaborated again 1 = None
    && Core_elaborate.roles elaborated rewritten 2 = None);
  check "the globals the declaration names, applied or not, are referenced"
    (List.sort GlobRef.UserOrd.compare (Core_elaborate.referenced elaborated)
    = List.sort GlobRef.UserOrd.compare [f; r "pa"]);
  Core_elaborate.install elaborated;
  Common.end_planning ();
  ignore (Core_elaborate.elaboration ~lex:Lexenv.empty rewritten [a]);
  ignore (Core_elaborate.elaboration ~lex:Lexenv.empty again [a]);
  (* The argument, a global named unapplied, is planned as its call with no
     arguments. *)
  check "a call whose use was rewritten is found planned, one built afresh is not"
    (Core_elaborate.report ()
    = "elaborated calls: 2 planned; emission found 1, elaborated 1 itself")
