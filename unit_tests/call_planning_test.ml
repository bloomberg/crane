(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Call planning on Core alone (Milestone 5's acceptance test): a call's
   instantiation -- a partial application's eta reading, a hole filled from
   an argument's type, a hole a full application leaves, a self-call -- the
   facts the elaboration walk records for a unit (closed heads, member
   templates, static projections, closed instances, singleton dictionaries,
   shared constants, match kinds), canonical spines, numeral folding where
   nothing is registered, and match-kind classification.  Every input is a
   Core term, an ML type or a table entry; no CppIR value is built. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "call_planning: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []}
let v i = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i}
let occ = Core.Occurrence.fresh
let id s = Core.Binder_name.Source (Id.of_string s)

let declare s ty =
  Table.add_type (r s) ty;
  Core.Expr.Global (Core.Global_use.monomorphic (r s))

let mono s = Core.Global_use.monomorphic (r s)

(* A use of [f] whose every variable is a hole: written nowhere. *)
let unwritten f ~arity =
  let scheme = Scheme.Id.fresh f ~arity in
  Core.Global_use.polymorphic f
    (Scheme.Instantiation.make scheme (fun _ ->
         {Scheme.solution = Scheme.Type (Core.Type.Hole (Scheme.Hole.fresh ())); source = Scheme.Not_written} ) )

let instantiate ?(lex = Lexenv.empty) ?caller ?(scope = []) use args =
  Core_elaborate.instantiate ~lex ~expected_core:None ~stated_core:None ~caller ~scope
    (Core_elaborate.elaborate_arguments ~lex use args)

(* The type the reading gives the callee's variable [i], where it gives one. *)
let var_type (inst : Elaborated_call.instantiated) i =
  List.find_map
    (fun (var, ty) -> if Scheme.Var.ordinal var = i then Some ty else None)
    (Core_util.Var_types.bindings inst.tys)

let mutind m l = MutInd.make1 (KerName.make (ModPath.MPfile (DirPath.make [Id.of_string m])) (Label.make l))
let unit_path = ModPath.MPfile (DirPath.make [Id.of_string "CP"])

(* A unit of the given declarations, walked: what lowering reads the
   walk's facts from. *)
let walk decls =
  Core_elaborate.structure ~methods:(fun _ _ -> [])
    [(unit_path, List.map (fun d -> (Label.make "d", Core.Module.Structure_item.Declaration d)) decls)]

(* The walk's answers are told apart from the live ones by asking in an
   environment, or of a term, that disagrees; under [CRANE_CHECK_IR] that
   disagreement is a violation, so those checks run only without it. *)
let checking = Probe.checking ()

(* A partial application is eta-expanded into a lambda spelled in the
   caller's scope: a callee variable nothing instantiates is bound by the
   lambda, and erased where its spelling is one of the caller's. *)
let () =
  let a = declare "pa" nat in
  let f = r "pf" in
  Table.add_type f (Core.Type.Arrow {parameter = v 1; result = Core.Type.Arrow {parameter = v 1; result = v 2}});
  let partial = instantiate (unwritten f ~arity:2) [a] in
  check "a partial application binds the variables it leaves open"
    (var_type partial 1 = Some (v 1) && var_type partial 2 = Some (v 2));
  check "the eta lambda's variables are said to come from it"
    (Call_tyargs.resolved_from Call_tyargs.Eta_parameter partial.reading);
  let colliding = instantiate ~scope:[Id.of_string "T2"] (unwritten f ~arity:2) [a] in
  check "a codomain variable spelled like a caller's is erased, not misread"
    (var_type colliding 2 = Some Core.Type.Unknown && var_type colliding 1 = Some (v 1));
  let self = instantiate ~caller:f (unwritten f ~arity:2) [a] in
  check "a self-call reads its variables as the caller's own"
    (Core_util.Var_types.is_empty self.tys
    && not (Call_tyargs.resolved_from Call_tyargs.Eta_parameter self.reading));
  let full = instantiate (unwritten f ~arity:2) [a; a] in
  check "a full application leaves its holes to deduction"
    (Core_util.Var_types.is_empty full.tys && Call_tyargs.holes full.reading <> []);
  check "the declared parameters are the callee's, at any arity"
    (Param_pos.to_list full.params_orig = [v 1; v 1]
    && Param_pos.to_list partial.params_orig = [v 1; v 1])

(* A variable only a function-typed parameter names is one C++ cannot
   deduce, so a partial application fills it from the argument's type. *)
let () =
  let g = declare "fg" (Core.Type.Arrow {parameter = nat; result = nat}) and b = declare "fb" nat in
  let f = r "ff" in
  Table.add_type f (Core.Type.Arrow {parameter = Core.Type.Arrow {parameter = v 1; result = nat};
                                     result = Core.Type.Arrow {parameter = nat; result = v 1}});
  let partial = instantiate (unwritten f ~arity:1) [g] in
  check "an undeducible hole is filled from the argument's type" (var_type partial 1 = Some nat);
  check "and says so" (Call_tyargs.resolved_from Call_tyargs.Argument_types partial.reading);
  check "the callee's type is instantiated at the filled reading"
    (partial.callee_type_at_call = Core.Type.Arrow
      {parameter = Core.Type.Arrow {parameter = nat; result = nat};
        result = Core.Type.Arrow {parameter = nat; result = nat}});
  check "its parameters too"
    (Param_pos.to_list partial.params = [Core.Type.Arrow {parameter = nat; result = nat}; nat]);
  let full = instantiate (unwritten f ~arity:1) [g; b] in
  check "a full application is not eta-expanded, so nothing is filled"
    (not (Call_tyargs.resolved_from Call_tyargs.Argument_types full.reading))

(* An argument past the callee's arity is applied to its result: the
   instantiation is of the callee's own parameters, and the excess argument
   is the call's to apply. *)
let () =
  let a = declare "xa" nat in
  let k = r "xk" in
  Table.add_type k (Core.Type.Arrow {parameter = nat; result = nat});
  let over = instantiate (Core.Global_use.monomorphic k) [a; a] in
  check "an over-application's excess is not a parameter"
    (over.call.excess = [a] && over.call.primary = [a] && Param_pos.to_list over.params = [nat]);
  check "its declared position maps to the same parameter"
    (Option.bind (over.subst_index_of_orig (Param_pos.of_regular ~leading:0 0)) (Param_pos.nth over.params)
    = Some nat);
  let dummy =
    instantiate (Core.Global_use.monomorphic k) [Core.Expr.Erased_value Core.Erasure_reason.Type_argument; a] in
  check "an erased argument at a value domain stays, so the call's arity does not change"
    (dummy.call.excess = [a] && dummy.call.roles = [Elaborated_call.Regular; Excess])

(* The facts the walk records, from the call and the binders of the walk's
   own environment, read back by lowering after the unit is installed.  A
   class [C] with one field [fld], polymorphic in a variable of its own, so
   that the instance declares it as a member template. *)
let () =
  let kn = mutind "CP" "C" in
  let fld = r "fld" and fld_mono = r "fld_mono" in
  Table.add_inductive_kind kn
    (Core.Inductive.Kind.Type_class
       [ {Core.Record.Field.projection = Some fld; type_ = Core.Type.Arrow {parameter = v 1; result = v 1}};
         {Core.Record.Field.projection = Some fld_mono; type_ = Core.Type.Arrow {parameter = nat; result = nat}} ]);
  let cls = Core.Type.Global_app {head = GlobRef.IndRef (kn, 0); type_arguments = []; index_arguments = []} in
  Table.add_type fld (Core.Type.Arrow {parameter = cls; result = Core.Type.Arrow {parameter = v 1; result = v 1}});
  Table.add_type fld_mono (Core.Type.Arrow {parameter = cls; result = Core.Type.Arrow {parameter = nat; result = nat}});
  let g = r "cg" in
  Table.add_type g (Core.Type.Arrow {parameter = cls; result = Core.Type.Arrow {parameter = nat; result = nat}});
  let c = declare "cc" nat in
  (* [d inst y := (g inst c y, g inst y y, fld inst y, fld_mono inst y)],
     each a call the walk meets with [inst] the declaration's dictionary. *)
  let inst () = Core.Expr.fresh_rel 2 and y () = Core.Expr.fresh_rel 1 in
  let closed = Core.Global_use.monomorphic g and open_ = Core.Global_use.monomorphic g in
  let member = Core.Global_use.polymorphic fld
      (Scheme.Instantiation.make (Scheme.Id.fresh fld ~arity:1) (fun _ ->
           {Scheme.solution = Scheme.Type nat; source = Scheme.Not_written} ) ) in
  let plain = Core.Global_use.monomorphic fld_mono in
  let body =
    Core.Expr.Tuple
      [ Core.Expr.Apply {callee = Core.Expr.Global closed; arguments = [inst (); c; y ()]};
        Core.Expr.Apply {callee = Core.Expr.Global open_; arguments = [inst (); y (); y ()]};
        Core.Expr.Apply {callee = Core.Expr.Global member; arguments = [inst (); y ()]};
        Core.Expr.Apply {callee = Core.Expr.Global plain; arguments = [inst (); y ()]} ]
  in
  let d = r "cd" in
  let dty = Core.Type.Arrow {parameter = cls; result = Core.Type.Arrow {parameter = nat; result = nat}} in
  let t =
    walk
      [Core.Decl.Value
        {entity = d;
          body = Core.Expr.Lambda
            {parameter = id "inst"; parameter_type = cls;
              body = Core.Expr.Lambda {parameter = id "y"; parameter_type = nat; body}}; type_ = dty}] in
  check "the declaration's class-typed parameter is its dictionary"
    (Core_elaborate.roles t closed 3 = Some [Elaborated_call.Dictionary; Regular; Excess]);
  let lex =
    Lexenv.push
      [ {Lexenv.eb_id = Id.of_string "y"; eb_type = nat; eb_role = Lexenv.Value};
        {eb_id = Id.of_string "inst"; eb_type = cls; eb_role = Dictionary} ]
      Lexenv.empty
  in
  let args_closed = [inst (); c; y ()] and args_open = [inst (); y (); y ()] in
  check "a head of the dictionary and a global is closed"
    (Core_elaborate.closed_head_call ~walk:(Some t) ~lex closed args_closed);
  check "a head naming a value binder is not"
    (not (Core_elaborate.closed_head_call ~walk:(Some t) ~lex open_ args_open));
  check "a projection through a kept instance of a polymorphic field is a member template"
    (Core_elaborate.member_template_call ~walk:(Some t) ~lex member [inst (); y ()]);
  check "one of a field with no variable of its own is not"
    (not (Core_elaborate.member_template_call ~walk:(Some t) ~lex plain [inst (); y ()]));
  check "a field neither mapped nor a singleton's method is no static projection"
    (Core_elaborate.static_projection_call ~walk:(Some t) ~lex member [inst (); y ()] = None);
  check "a call of a global Rocq does not know is no closed instance"
    (not (Core_elaborate.closed_instance_call ~walk:(Some t) ~lex closed args_closed));
  if not checking then (
    (* Asked in an environment with no binders, the live answer differs:
       the walk's is the one given. *)
    check "the closed head is the walk's, not the asker's environment's"
      (Core_elaborate.closed_head_call ~walk:(Some t) ~lex:Lexenv.empty closed args_closed);
    check "the member template is the walk's"
      (Core_elaborate.member_template_call ~walk:(Some t) ~lex:Lexenv.empty member [inst (); y ()]);
    check "a singleton dictionary the walk did not find there is none, whatever the asker says"
      (Core_elaborate.singleton_dictionary_call ~walk:(Some t) ~live:(fun () -> Some (d, d)) (occ ()) = None) )

(* A shared constant is a construction of a shared variant, which only
   [Set Crane SharedVariant] makes one: setting that option needs a Rocq
   library session, so here an inductive registered as shared is still no
   shared variant, and the walk records each construction as no constant,
   by its occurrence. *)
let () =
  let kn = mutind "CP" "S" in
  let ind = GlobRef.IndRef (kn, 0) in
  Table.add_shared_variant ind;
  let ty = Core.Type.Global_app {head = ind; type_arguments = []; index_arguments = []} in
  let ctor = GlobRef.ConstructRef ((kn, 0), 1) in
  let constant = Core.Expr.Construct {result_type = ty;
                                      constructor = ctor;
                                      arguments =
                                        [Core.Expr.UInt63 (Uint63.of_int 3);
                                          Core.Expr.Erased_value Core.Erasure_reason.Proof];
                                      occurrence = occ ()} in
  check "without the option no construction is a shared constant"
    ((not (Table.is_shared_variant ind)) && not (Core_elaborate.shared_constant ~walk:None constant));
  let walk = Some (walk [Core.Decl.Value {entity = r "sd"; body = constant; type_ = ty}]) in
  check "the walk agrees for the occurrence" (not (Core_elaborate.shared_constant ~walk constant));
  check "a term that is no construction is never one"
    (not (Core_elaborate.shared_constant ~walk (Core.Expr.UInt63 (Uint63.of_int 3))))

(* How a match is lowered, from its annotated type and branches alone. *)
let () =
  let kn = mutind "CP" "R" and kc = mutind "CP" "K" in
  let fx = r "rx" and fy = r "ry" in
  Table.add_inductive_kind kn
    (Core.Inductive.Kind.Record
       [ {Core.Record.Field.projection = Some fx; type_ = nat};
         {Core.Record.Field.projection = Some fy; type_ = Core.Type.Arrow {parameter = nat; result = nat}} ]);
  Table.add_inductive_kind kc (Core.Inductive.Kind.Type_class [{Core.Record.Field.projection = Some fx; type_ = nat}]);
  let rec_ty = Core.Type.Global_app {head = GlobRef.IndRef (kn, 0);
                                     type_arguments = [];
                                     index_arguments = []}
                                       and cls_ty =
                                         Core.Type.Global_app
                                           {head = GlobRef.IndRef (kc, 0); type_arguments = []; index_arguments = []} in
  let pat = Core.Pattern.binding_all (GlobRef.ConstructRef ((kn, 0), 1)) 2 in
  let ids = [(id "x", nat); (id "y", Core.Type.Arrow {parameter = nat; result = nat})] in
  let one body = [|{Core.Match.Branch.binders = ids; result_type = nat; pattern = pat; body = body}|] in
  let a = declare "ma" nat in
  let kind = Match_kind.classify rec_ty in
  check "reading the first field is a projection of field 0"
    (kind (one (Core.Expr.fresh_rel 2)) = Record
      {typeclass = false; body = Projection {field = 0; application = Read}});
  check "calling the second is a call projection"
    (kind (one (Core.Expr.Apply {callee = Core.Expr.fresh_rel 1;
                                 arguments = [a]})) = Record
                                   {typeclass = false; body = Projection {field = 1; application = Call}});
  check "calling it through a coercion is a coerced call"
    (kind (one (Core.Expr.Apply {callee = Core.Expr.Boxed_value {value = Core.Expr.fresh_rel 1; occurrence = occ ()};
                                 arguments = [a]}))
    = Record {typeclass = false; body = Projection {field = 1; application = Coerced_call}});
  check "a projection is looked at through one coercion"
    (kind (one (Core.Expr.Boxed_value {value = Core.Expr.fresh_rel 2; occurrence = occ ()}))
    = Record {typeclass = false; body = Projection {field = 0; application = Read}});
  check "a variable bound outside the branch is no projection"
    (kind (one (Core.Expr.fresh_rel 3)) = Record {typeclass = false; body = Destructure});
  check "any other body destructures" (kind (one a) = Record {typeclass = false; body = Destructure});
  check "a class's dictionary is a record match marked typeclass"
    (Match_kind.classify cls_ty
       [|{Core.Match.Branch.binders = [(id "x", nat)]; result_type = nat; pattern = pat; body = Core.Expr.fresh_rel 1}|]
    = Record {typeclass = true; body = Projection {field = 0; application = Read}});
  let both = {Core.Match.Branch.binders = ids; result_type = nat; pattern = pat; body = a} in
  check "two branches are a variant" (kind [|both; both|] = Variant);
  check "one branch over no record is a variant" (Match_kind.classify nat (one a) = Variant);
  check "a record match is bound in place, a variant is not"
    (Match_kind.bound_in_place (kind (one a)) && Match_kind.is_record (kind (one a))
    && (not (Match_kind.bound_in_place Variant)) && not (Match_kind.is_record Variant));
  (* The walk records the kind by the match's occurrence. *)
  let at = occ () in
  let m = Core.Expr.Match {scrutinee_type = rec_ty;
                           scrutinee = a;
                           branches = one (Core.Expr.fresh_rel 2);
                           occurrence = at} in
  let walk = Some (walk [Core.Decl.Value {entity = r "md"; body = m; type_ = nat}]) in
  check "lowering reads the kind the walk recorded"
    (Core_elaborate.match_kind ~walk rec_ty (one (Core.Expr.fresh_rel 2)) at
    = Record {typeclass = false; body = Projection {field = 0; application = Read}});
  if not checking then
    check "the recorded kind stands for the occurrence, whatever type it is asked at"
      (Core_elaborate.match_kind ~walk nat (one (Core.Expr.fresh_rel 2)) at
      = Record {typeclass = false; body = Projection {field = 0; application = Read}})

(* Canonical spines: each call read whole, written once. *)
let () =
  let f = mono "nf" and a = declare "na" nat and b = declare "nb" nat in
  Table.add_type (r "nf") (Core.Type.Arrow {parameter = nat; result = Core.Type.Arrow {parameter = nat; result = nat}});
  let staged = Core.Expr.Apply {callee = Core.Expr.Apply {callee = Core.Expr.Global f; arguments = [a]};
                                arguments = [b]} in
  check "a staged application is not canonical" (not (Core_normalize.is_canonical staged));
  check "a global applied in stages is applied once"
    (Core_normalize.spine staged = Core.Expr.Apply {callee = Core.Expr.Global f; arguments = [a; b]});
  check "a coercion of the head is dropped"
    (Core_normalize.apply (Core.Expr.Boxed_value {value = Core.Expr.Global f; occurrence = occ ()}) [a; b] =
      Core.Expr.Apply {callee = Core.Expr.Global f; arguments = [a; b]});
  check "an erased head is itself, its arguments never evaluated"
    (Core_normalize.apply (Core.Expr.Erased_value Core.Erasure_reason.Proof) [a] = Core.Expr.Erased_value
      Core.Erasure_reason.Proof
    && Core_normalize.apply (Core.Expr.Runtime_error "absurd") [a] = Core.Expr.Runtime_error "absurd");
  (* [(let (x, y) := p in g x) a] is [let (x, y) := p in g x a]: the
     argument is lifted past the branch's binders. *)
  let ids = [(id "x", nat); (id "y", nat)] in
  let mocc = occ () in
  let destructure body =
    Core.Expr.Match {scrutinee_type = nat;
                     scrutinee = a;
                     branches = [|{Core.Match.Branch.binders = ids;
                                   result_type = nat;
                                   pattern = Core.Pattern.Wildcard;
                                   body = body}|];
                     occurrence = mocc}
  in
  ( match Core_normalize.apply
    (destructure (Core.Expr.Apply {callee = Core.Expr.Global f; arguments = [Core.Expr.fresh_rel 2]}))
      [Core.Expr.fresh_rel 1] with
  | Core.Expr.Match
    {branches =
      [|{Core.Match.Branch.body = Core.Expr.Apply
          {callee = Core.Expr.Global f';
            arguments = [Core.Expr.Bound_variable {index = 2; _}; Core.Expr.Bound_variable {index = 3; _}]}; _}|];
                     occurrence = o; _} ->
    check "a destructuring's branch takes the argument, lifted"
      (Core.Global_use.callee f' = r "nf" && Core.Occurrence.equal o mocc)
  | _ -> check "applying a one-branch match applies its branch" false );
  let local = Core.Expr.Apply {callee = Core.Expr.fresh_rel 1; arguments = [a]} in
  check "a variable head is canonical" (Core_normalize.canonical_application local);
  check "a nested staged application is made canonical under a lambda"
    (Core_normalize.spine (Core.Expr.Lambda {parameter = id "z"; parameter_type = nat; body = staged}) =
      Core.Expr.Lambda
        {parameter = id "z"; parameter_type = nat;
          body = Core.Expr.Apply {callee = Core.Expr.Global f; arguments = [a; b]}});
  check "spine makes every application canonical"
    (Core_normalize.is_canonical
      (Core_normalize.spine
        (Core.Expr.Tuple
          [staged;
            destructure
              (Core.Expr.Apply
                {callee = Core.Expr.Apply {callee = Core.Expr.Global f; arguments = [a]}; arguments = [b]})])));
  check "spine leaves a canonical term alone" (Core_normalize.spine local = local)

(* A constructor chain of an inductive no numeral mapping names is no
   literal, and a global no mapping names is no converter. *)
let () =
  let kn = mutind "CP" "N" in
  let zero = GlobRef.ConstructRef ((kn, 0), 1) and succ = GlobRef.ConstructRef ((kn, 0), 2) in
  let ty = Core.Type.Global_app {head = GlobRef.IndRef (kn, 0); type_arguments = []; index_arguments = []} in
  let two = Core.Expr.Construct {result_type = ty;
                                 constructor = succ;
                                 arguments =
                                   [Core.Expr.Construct
                                     {result_type = ty; constructor = succ;
                                       arguments =
                                         [Core.Expr.Construct
                                           {result_type = ty; constructor = zero; arguments = []; occurrence = occ ()}];
                                             occurrence = occ ()}];
                                 occurrence = occ ()} in
  check "an unregistered Peano chain does not fold"
    ((not (Numeral_literal.folds two)) && Numeral_literal.fold two == two
    && Numeral_literal.constructor_literal two = None);
  check "spine leaves it a construction" (Core_normalize.spine two = two && Core_normalize.canonical_application two);
  let conv = Core.Expr.Apply {callee = Core.Expr.Global (mono "nconv"); arguments = [two]} in
  check "a global no mapping names is no numeral converter"
    ((not (Numeral_literal.converter_folds conv)) && Numeral_literal.converter_literal (r "nconv") two = None);
  check "no constructor of an unregistered inductive is a registered digit"
    (Numeral_literal.registered_constructor "num.uint.type" zero = None)
