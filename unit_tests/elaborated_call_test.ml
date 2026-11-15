(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* A call as Core elaborates it, from the callee's type, the call's arguments
   and the lexical environment they are typed in alone: no C++ type is
   chosen, no expression generated, and no translation state is read. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "elaborated_call: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []}

let declare s ty =
  Table.add_type (r s) ty;
  Core.Expr.Global (Core.Global_use.monomorphic (r s))

let binder ?(role = Lexenv.Value) s ty = {Lexenv.eb_id = Id.of_string s; eb_type = ty; eb_role = role}

let elaborate ?(lex = Lexenv.empty) f args =
  Core_elaborate.elaborate_arguments ~lex (Core.Global_use.monomorphic f) args

let () =
  let a = declare "a" nat and b = declare "b" nat and c = declare "c" nat in
  let f = r "f" in
  Table.add_type f (Core.Type.Arrow {parameter = nat; result = Core.Type.Arrow {parameter = nat; result = nat}});
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
  Table.add_type g (Core.Type.Arrow {parameter = nat;
                                     result = Core.Type.Arrow {parameter = Core.Type.Erased Core.Erasure_reason.Type_argument;
                                                               result = Core.Type.Arrow {parameter = nat;
                                                                                         result = nat}}});
  let eta = elaborate g [a; Core.Expr.Erased_value Core.Erasure_reason.Type_argument; b] in
  check "a dummy at an erased domain is not a value argument"
    (eta.primary = [a; b] && eta.excess = []
    && eta.roles = [Elaborated_call.Regular; Dropped; Regular]);
  check "the callee's declared type is kept" (eta.callee_type = Table.find_type g)

(* A variable argument is a dictionary by the role its binder was bound
   with, not by its name: a declaration's class-typed parameter is one, a
   class-typed binder inside the body is a value. *)
let () =
  let kn = MutInd.make1 (KerName.make (ModPath.MPfile (DirPath.make [Id.of_string "T"])) (Label.make "C")) in
  Table.add_inductive_kind kn (Core.Inductive.Kind.Type_class []);
  let class_ty = Core.Type.Global_app {head = GlobRef.IndRef (kn, 0); type_arguments = []; index_arguments = []} in
  let h = r "h" in
  Table.add_type h (Core.Type.Arrow {parameter = class_ty; result = Core.Type.Arrow {parameter = nat; result = nat}});
  let lex = Lexenv.push [binder "x" nat; binder ~role:Lexenv.Dictionary "inst" class_ty] Lexenv.empty in
  let call = elaborate ~lex h [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1] in
  check "a declaration's class-typed parameter is passed as its dictionary"
    (call.instances = [Core.Expr.fresh_rel 2] && call.regular = [Core.Expr.fresh_rel 1]
    && call.roles = [Elaborated_call.Dictionary; Regular]);
  check "the dictionary occupies the leading parameter" (Elaborated_call.leading_params call = 1);
  let lex = Lexenv.push [binder "inst" class_ty; binder "x" nat] Lexenv.empty in
  let local = elaborate ~lex h [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 2] in
  check "a class-typed binder bound in a body is a value" (local.instances = [])

(* A call is found among the ones planned from Core by its use's occurrence,
   which survives the annotation rewrites a body goes through before it is
   translated: a polymorphic use is rebuilt by every rewrite of its types. *)
let () =
  let f = r "pf" in
  Table.add_type f (Core.Type.Arrow {parameter = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                                     variable = 1};
                                     result = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                                  variable = 1}});
  let scheme = Scheme.Id.fresh f ~arity:1 in
  let at_nat () =
    Core.Global_use.polymorphic f
      (Scheme.Instantiation.make scheme (fun _ ->
           {Scheme.solution = Scheme.Type nat; source = Scheme.Not_written} ) )
  in
  let use = at_nat () in
  let rewritten = Core.Global_use.map_types Fun.id use in
  check "a rewrite of a use's types keeps its occurrence"
    (Core.Occurrence.equal (Core.Global_use.occurrence use) (Core.Global_use.occurrence rewritten));
  let again = at_nat () in
  check "a use built afresh is another occurrence"
    (not (Core.Occurrence.equal (Core.Global_use.occurrence use) (Core.Global_use.occurrence again)));
  check "occurrences do not tell terms apart structurally" (Core.Expr.Global use = Core.Expr.Global again);
  let a = declare "pa" nat in
  let unit = ModPath.MPfile (DirPath.make [Id.of_string "U"]) in
  let elaborated =
    Core_elaborate.structure ~methods:(fun _ _ -> [])
      [(unit, [(Label.make "d", Core.Module.Structure_item.Declaration (Core.Decl.Value {entity = r "d"; body = Core.Expr.Apply {callee = Core.Expr.Global use; arguments = [a]}; type_ = nat}))])]
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
  Common.end_planning ();
  let walk = Some elaborated in
  ignore (Core_elaborate.elaboration ~walk ~lex:Lexenv.empty rewritten [a]);
  ignore (Core_elaborate.elaboration ~walk ~lex:Lexenv.empty again [a]);
  (* The argument, a global named unapplied, is planned as its call with no
     arguments. *)
  check "a call whose use was rewritten is found planned, one built afresh is not"
    (Core_elaborate.report elaborated
    = "elaborated calls: 2 planned; emission found 1, elaborated 1 itself; took 0 instantiations planned, \
       0 instantiated itself");
  (* Its instantiation is the walk's, taken at the argument nodes being
     translated, which a rewrite rebuilt. *)
  let a' = match a with Core.Expr.Global u -> Core.Expr.Global (Core.Global_use.map_types Fun.id u) | e -> e in
  let inst =
    Core_elaborate.instantiation ~walk ~lex:Lexenv.empty ~expected_core:None ~stated_core:None ~caller:None ~scope:[]
      rewritten [a']
  in
  check "a call's instantiation is the one planned, at the arguments translated"
    (Elaborated_call.same_instantiation inst
       (Core_elaborate.instantiate ~lex:Lexenv.empty ~expected_core:None ~stated_core:None ~caller:None ~scope:[]
          (Core_elaborate.elaborate_arguments ~lex:Lexenv.empty rewritten [a']) )
    && List.equal ( == ) inst.call.args [a']
    && Core_elaborate.report elaborated
       = "elaborated calls: 2 planned; emission found 2, elaborated 1 itself; took 1 instantiations planned, \
          0 instantiated itself")

(* The semantic half of planning a call is decided from Core alone: the
   callee's declared type, the call's reading of its variables, and the
   lexical environment -- no translation state, no C++ type. *)
let () =
  let f = r "pk" in
  let a1 = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1} in
  Table.add_type f (Core.Type.Arrow {parameter = a1;
                                     result = Core.Type.Arrow {parameter = Core.Type.Erased Core.Erasure_reason.Type_argument;
                                                               result = Core.Type.Arrow {parameter = a1;
                                                                                         result = a1}}});
  let scheme = Scheme.Id.fresh f ~arity:1 in
  let use =
    Core.Global_use.polymorphic f
      (Scheme.Instantiation.make scheme (fun _ ->
           { Scheme.solution = Scheme.Type nat;
             source = Scheme.Written {binder = Scheme.Binder.of_position 0; observed = Some nat} } ) )
  in
  let a = declare "ka" nat and b = declare "kb" nat in
  let inst =
    Core_elaborate.instantiate ~lex:Lexenv.empty ~expected_core:None ~stated_core:None ~caller:None
      ~scope:[] (Core_elaborate.elaborate_arguments ~lex:Lexenv.empty use [a; b])
  in
  check "the callee's type is instantiated at the reading"
    (inst.callee_type_at_call = Core.Type.Arrow {parameter = nat;
                                                 result = Core.Type.Arrow {parameter = Core.Type.Erased Core.Erasure_reason.Type_argument;
                                                                           result = Core.Type.Arrow {parameter = nat;
                                                                                                     result = nat}}});
  check "the declared parameters are the callee's own, its erased domain none of them"
    (Param_pos.to_list inst.params_orig = [a1; a1]);
  check "the instantiated parameters are at the reading"
    (Param_pos.to_list inst.params = [nat; nat]);
  check "a declared position names the same parameter after substitution"
    (Option.bind (inst.subst_index_of_orig (Param_pos.of_regular ~leading:0 0)) (Param_pos.nth inst.params)
    = Some nat);
  check "a call at its arity keeps the reading it was elaborated with"
    (Core_util.Var_types.equal inst.tys (Call_tyargs.by_variable inst.call.tyargs))

(* A function generated as a method of its inductive is generated, and its
   calls elaborated, at its variables renumbered so the inductive's come
   first: [fold_left]'s element variable, the receiver's, is the list's. *)
let () =
  let v i = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i} in
  let list t = Core.Type.Global_app {head = r "list"; type_arguments = [t]; index_arguments = []} in
  let fold_left = Core.Type.Arrow {parameter = Core.Type.Arrow {parameter = v 1;
                                                                result = Core.Type.Arrow {parameter = v 2;
                                                                                          result = v 1}};
                                   result = Core.Type.Arrow {parameter = list (v 2);
                                                             result = Core.Type.Arrow {parameter = v 1;
                                                                                       result = v 1}}} in
  let n = Method_registry.renumbering ~num_ind_vars:1 ~this_pos:1 fold_left in
  check "the receiver's variable is the inductive's, the function's own follow"
    (n.renamed && n.rename 2 = 1 && n.rename 1 = 2 && n.extra = [1]);
  check "the type is renumbered"
    (Method_registry.renumber_type n fold_left
    = Core.Type.Arrow {parameter = Core.Type.Arrow {parameter = v 2;
                                                    result = Core.Type.Arrow {parameter = v 1; result = v 2}};
                       result = Core.Type.Arrow {parameter = list (v 1);
                                                 result = Core.Type.Arrow {parameter = v 2; result = v 2}}});
  let map = Core.Type.Arrow {parameter = Core.Type.Arrow {parameter = v 1; result = v 2};
                             result = Core.Type.Arrow {parameter = list (v 1); result = list (v 2)}} in
  let n = Method_registry.renumbering ~num_ind_vars:1 ~this_pos:1 map in
  check "variables already in place are left, the function's own still counted"
    (n.renamed && n.rename 1 = 1 && n.rename 2 = 2 && n.extra = [2])
