(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Call planning on Core alone (Milestone 5's acceptance test): a call's
   instantiation -- a partial application's eta reading, a hole filled from
   an argument's type, a hole a full application leaves, a self-call -- the
   facts the elaboration walk records for a unit (closed heads, member
   templates, static projections, closed instances, singleton dictionaries,
   shared constants, match kinds), canonical spines, numeral folding where
   nothing is registered, and match-kind classification.  Every input is a
   Core term, an ML type or a table entry; no MiniCpp or CppIR value is
   built. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "call_planning: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let nat = Tglob (r "nat", [], [])
let v i = Tvar (Schematic, i)
let occ = Occurrence.fresh
let id s = Id (Id.of_string s)

let declare s ty =
  Table.add_type (r s) ty;
  MLglob (Global_use.monomorphic (r s))

let mono s = Global_use.monomorphic (r s)

(* A use of [f] whose every variable is a hole: written nowhere. *)
let unwritten f ~arity =
  let scheme = Scheme.Id.fresh f ~arity in
  Global_use.polymorphic f
    (Scheme.Instantiation.make scheme (fun _ ->
         {Scheme.solution = Scheme.Type (Thole (Scheme.Hole.fresh ())); source = Scheme.Not_written} ) )

let instantiate ?(lex = Lexenv.empty) ?caller ?(scope = []) use args =
  Core_elaborate.instantiate ~lex ~expected_ml:None ~stated_ml:None ~caller ~scope
    (Core_elaborate.elaborate_arguments ~lex use args)

(* The type the reading gives the callee's variable [i], where it gives one. *)
let var_type (inst : Elaborated_call.instantiated) i =
  List.find_map
    (fun (var, ty) -> if Scheme.Var.ordinal var = i then Some ty else None)
    (Mlutil.Var_types.bindings inst.tys)

let mutind m l = MutInd.make1 (KerName.make (ModPath.MPfile (DirPath.make [Id.of_string m])) (Label.make l))
let unit_path = ModPath.MPfile (DirPath.make [Id.of_string "CP"])

(* A unit of the given declarations, walked and installed: what lowering
   reads the walk's facts from. *)
let walk_and_install decls =
  let t =
    Core_elaborate.structure ~methods:(fun _ _ -> [])
      [(unit_path, List.map (fun d -> (Label.make "d", SEdecl d)) decls)]
  in
  Core_elaborate.install t;
  t

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
  Table.add_type f (Tarr (v 1, Tarr (v 1, v 2)));
  let partial = instantiate (unwritten f ~arity:2) [a] in
  check "a partial application binds the variables it leaves open"
    (var_type partial 1 = Some (v 1) && var_type partial 2 = Some (v 2));
  check "the eta lambda's variables are said to come from it"
    (Call_tyargs.resolved_from Call_tyargs.Eta_parameter partial.reading);
  let colliding = instantiate ~scope:[Id.of_string "T2"] (unwritten f ~arity:2) [a] in
  check "a codomain variable spelled like a caller's is erased, not misread"
    (var_type colliding 2 = Some Tunknown && var_type colliding 1 = Some (v 1));
  let self = instantiate ~caller:f (unwritten f ~arity:2) [a] in
  check "a self-call reads its variables as the caller's own"
    (Mlutil.Var_types.is_empty self.tys
    && not (Call_tyargs.resolved_from Call_tyargs.Eta_parameter self.reading));
  let full = instantiate (unwritten f ~arity:2) [a; a] in
  check "a full application leaves its holes to deduction"
    (Mlutil.Var_types.is_empty full.tys && Call_tyargs.holes full.reading <> []);
  check "the declared parameters are the callee's, at any arity"
    (Param_pos.to_list full.params_orig = [v 1; v 1]
    && Param_pos.to_list partial.params_orig = [v 1; v 1])

(* A variable only a function-typed parameter names is one C++ cannot
   deduce, so a partial application fills it from the argument's type. *)
let () =
  let g = declare "fg" (Tarr (nat, nat)) and b = declare "fb" nat in
  let f = r "ff" in
  Table.add_type f (Tarr (Tarr (v 1, nat), Tarr (nat, v 1)));
  let partial = instantiate (unwritten f ~arity:1) [g] in
  check "an undeducible hole is filled from the argument's type" (var_type partial 1 = Some nat);
  check "and says so" (Call_tyargs.resolved_from Call_tyargs.Argument_types partial.reading);
  check "the callee's type is instantiated at the filled reading"
    (partial.callee_type_at_call = Tarr (Tarr (nat, nat), Tarr (nat, nat)));
  check "its parameters too" (Param_pos.to_list partial.params = [Tarr (nat, nat); nat]);
  let full = instantiate (unwritten f ~arity:1) [g; b] in
  check "a full application is not eta-expanded, so nothing is filled"
    (not (Call_tyargs.resolved_from Call_tyargs.Argument_types full.reading))

(* An argument past the callee's arity is applied to its result: the
   instantiation is of the callee's own parameters, and the excess argument
   is the call's to apply. *)
let () =
  let a = declare "xa" nat in
  let k = r "xk" in
  Table.add_type k (Tarr (nat, nat));
  let over = instantiate (Global_use.monomorphic k) [a; a] in
  check "an over-application's excess is not a parameter"
    (over.call.excess = [a] && over.call.primary = [a] && Param_pos.to_list over.params = [nat]);
  check "its declared position maps to the same parameter"
    (Option.bind (over.subst_index_of_orig (Param_pos.of_regular ~leading:0 0)) (Param_pos.nth over.params)
    = Some nat);
  let dummy = instantiate (Global_use.monomorphic k) [MLdummy Ktype; a] in
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
    (Core.Inductive.Kind.Type_class [(Some fld, Tarr (v 1, v 1)); (Some fld_mono, Tarr (nat, nat))]);
  let cls = Tglob (GlobRef.IndRef (kn, 0), [], []) in
  Table.add_type fld (Tarr (cls, Tarr (v 1, v 1)));
  Table.add_type fld_mono (Tarr (cls, Tarr (nat, nat)));
  let g = r "cg" in
  Table.add_type g (Tarr (cls, Tarr (nat, nat)));
  let c = declare "cc" nat in
  (* [d inst y := (g inst c y, g inst y y, fld inst y, fld_mono inst y)],
     each a call the walk meets with [inst] the declaration's dictionary. *)
  let inst () = fresh_rel 2 and y () = fresh_rel 1 in
  let closed = Global_use.monomorphic g and open_ = Global_use.monomorphic g in
  let member = Global_use.polymorphic fld
      (Scheme.Instantiation.make (Scheme.Id.fresh fld ~arity:1) (fun _ ->
           {Scheme.solution = Scheme.Type nat; source = Scheme.Not_written} ) ) in
  let plain = Global_use.monomorphic fld_mono in
  let body =
    MLtuple
      [ MLapp (MLglob closed, [inst (); c; y ()]);
        MLapp (MLglob open_, [inst (); y (); y ()]);
        MLapp (MLglob member, [inst (); y ()]);
        MLapp (MLglob plain, [inst (); y ()]) ]
  in
  let d = r "cd" in
  let dty = Tarr (cls, Tarr (nat, nat)) in
  let t = walk_and_install [Dterm (d, MLlam (id "inst", cls, MLlam (id "y", nat, body)), dty)] in
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
    (Core_elaborate.closed_head_call ~lex closed args_closed);
  check "a head naming a value binder is not"
    (not (Core_elaborate.closed_head_call ~lex open_ args_open));
  check "a projection through a kept instance of a polymorphic field is a member template"
    (Core_elaborate.member_template_call ~lex member [inst (); y ()]);
  check "one of a field with no variable of its own is not"
    (not (Core_elaborate.member_template_call ~lex plain [inst (); y ()]));
  check "a field neither mapped nor a singleton's method is no static projection"
    (Core_elaborate.static_projection_call ~lex member [inst (); y ()] = None);
  check "a call of a global Rocq does not know is no closed instance"
    (not (Core_elaborate.closed_instance_call ~lex closed args_closed));
  if not checking then (
    (* Asked in an environment with no binders, the live answer differs:
       the walk's is the one given. *)
    check "the closed head is the walk's, not the asker's environment's"
      (Core_elaborate.closed_head_call ~lex:Lexenv.empty closed args_closed);
    check "the member template is the walk's"
      (Core_elaborate.member_template_call ~lex:Lexenv.empty member [inst (); y ()]);
    check "a singleton dictionary the walk did not find there is none, whatever the asker says"
      (Core_elaborate.singleton_dictionary_call ~live:(fun () -> Some (d, d)) (occ ()) = None) )

(* A shared constant is a construction of a shared variant, which only
   [Set Crane SharedVariant] makes one: setting that option needs a Rocq
   library session, so here an inductive registered as shared is still no
   shared variant, and the walk records each construction as no constant,
   by its occurrence. *)
let () =
  let kn = mutind "CP" "S" in
  let ind = GlobRef.IndRef (kn, 0) in
  Table.add_shared_variant ind;
  let ty = Tglob (ind, [], []) in
  let ctor = GlobRef.ConstructRef ((kn, 0), 1) in
  let constant = MLcons (ty, ctor, [MLuint (Uint63.of_int 3); MLdummy Kprop], occ ()) in
  check "without the option no construction is a shared constant"
    ((not (Table.is_shared_variant ind)) && not (Core_elaborate.shared_constant constant));
  ignore (walk_and_install [Dterm (r "sd", constant, ty)]);
  check "the walk agrees for the occurrence" (not (Core_elaborate.shared_constant constant));
  check "a term that is no construction is never one" (not (Core_elaborate.shared_constant (MLuint (Uint63.of_int 3))))

(* How a match is lowered, from its annotated type and branches alone. *)
let () =
  let kn = mutind "CP" "R" and kc = mutind "CP" "K" in
  let fx = r "rx" and fy = r "ry" in
  Table.add_inductive_kind kn (Core.Inductive.Kind.Record [(Some fx, nat); (Some fy, Tarr (nat, nat))]);
  Table.add_inductive_kind kc (Core.Inductive.Kind.Type_class [(Some fx, nat)]);
  let rec_ty = Tglob (GlobRef.IndRef (kn, 0), [], []) and cls_ty = Tglob (GlobRef.IndRef (kc, 0), [], []) in
  let pat = Pusual (GlobRef.ConstructRef ((kn, 0), 1)) in
  let ids = [(id "x", nat); (id "y", Tarr (nat, nat))] in
  let one body = [|(ids, nat, pat, body)|] in
  let a = declare "ma" nat in
  let kind = Match_kind.classify rec_ty in
  check "reading the first field is a projection of field 0"
    (kind (one (fresh_rel 2)) = Record {typeclass = false; body = Projection {field = 0; application = Read}});
  check "calling the second is a call projection"
    (kind (one (MLapp (fresh_rel 1, [a]))) = Record {typeclass = false; body = Projection {field = 1; application = Call}});
  check "calling it through a coercion is a coerced call"
    (kind (one (MLapp (MLmagic (Mboxed, fresh_rel 1, occ ()), [a])))
    = Record {typeclass = false; body = Projection {field = 1; application = Coerced_call}});
  check "a projection is looked at through one coercion"
    (kind (one (MLmagic (Mboxed, fresh_rel 2, occ ())))
    = Record {typeclass = false; body = Projection {field = 0; application = Read}});
  check "a variable bound outside the branch is no projection"
    (kind (one (fresh_rel 3)) = Record {typeclass = false; body = Destructure});
  check "any other body destructures" (kind (one a) = Record {typeclass = false; body = Destructure});
  check "a class's dictionary is a record match marked typeclass"
    (Match_kind.classify cls_ty [|([(id "x", nat)], nat, pat, fresh_rel 1)|]
    = Record {typeclass = true; body = Projection {field = 0; application = Read}});
  check "two branches are a variant" (kind [|(ids, nat, pat, a); (ids, nat, pat, a)|] = Variant);
  check "one branch over no record is a variant" (Match_kind.classify nat (one a) = Variant);
  check "a record match is bound in place, a variant is not"
    (Match_kind.bound_in_place (kind (one a)) && Match_kind.is_record (kind (one a))
    && (not (Match_kind.bound_in_place Variant)) && not (Match_kind.is_record Variant));
  (* The walk records the kind by the match's occurrence. *)
  let at = occ () in
  let m = MLcase (rec_ty, a, one (fresh_rel 2), at) in
  ignore (walk_and_install [Dterm (r "md", m, nat)]);
  check "lowering reads the kind the walk recorded"
    (Core_elaborate.match_kind rec_ty (one (fresh_rel 2)) at
    = Record {typeclass = false; body = Projection {field = 0; application = Read}});
  if not checking then
    check "the recorded kind stands for the occurrence, whatever type it is asked at"
      (Core_elaborate.match_kind nat (one (fresh_rel 2)) at
      = Record {typeclass = false; body = Projection {field = 0; application = Read}})

(* Canonical spines: each call read whole, written once. *)
let () =
  let f = mono "nf" and a = declare "na" nat and b = declare "nb" nat in
  Table.add_type (r "nf") (Tarr (nat, Tarr (nat, nat)));
  let staged = MLapp (MLapp (MLglob f, [a]), [b]) in
  check "a staged application is not canonical" (not (Core_normalize.is_canonical staged));
  check "a global applied in stages is applied once" (Core_normalize.spine staged = MLapp (MLglob f, [a; b]));
  check "a coercion of the head is dropped"
    (Core_normalize.apply (MLmagic (Mboxed, MLglob f, occ ())) [a; b] = MLapp (MLglob f, [a; b]));
  check "an erased head is itself, its arguments never evaluated"
    (Core_normalize.apply (MLdummy Kprop) [a] = MLdummy Kprop
    && Core_normalize.apply (MLexn "absurd") [a] = MLexn "absurd");
  (* [(let (x, y) := p in g x) a] is [let (x, y) := p in g x a]: the
     argument is lifted past the branch's binders. *)
  let ids = [(id "x", nat); (id "y", nat)] in
  let mocc = occ () in
  let destructure body = MLcase (nat, a, [|(ids, nat, Pwild, body)|], mocc) in
  ( match Core_normalize.apply (destructure (MLapp (MLglob f, [fresh_rel 2]))) [fresh_rel 1] with
  | MLcase (_, _, [|(_, _, _, MLapp (MLglob f', [MLrel (2, _); MLrel (3, _)]))|], o) ->
    check "a destructuring's branch takes the argument, lifted"
      (Global_use.callee f' = r "nf" && Occurrence.equal o mocc)
  | _ -> check "applying a one-branch match applies its branch" false );
  let local = MLapp (fresh_rel 1, [a]) in
  check "a variable head is canonical" (Core_normalize.canonical_application local);
  check "a nested staged application is made canonical under a lambda"
    (Core_normalize.spine (MLlam (id "z", nat, staged)) = MLlam (id "z", nat, MLapp (MLglob f, [a; b])));
  check "spine makes every application canonical"
    (Core_normalize.is_canonical (Core_normalize.spine (MLtuple [staged; destructure (MLapp (MLapp (MLglob f, [a]), [b]))])));
  check "spine leaves a canonical term alone" (Core_normalize.spine local = local)

(* A constructor chain of an inductive no numeral mapping names is no
   literal, and a global no mapping names is no converter. *)
let () =
  let kn = mutind "CP" "N" in
  let zero = GlobRef.ConstructRef ((kn, 0), 1) and succ = GlobRef.ConstructRef ((kn, 0), 2) in
  let ty = Tglob (GlobRef.IndRef (kn, 0), [], []) in
  let two = MLcons (ty, succ, [MLcons (ty, succ, [MLcons (ty, zero, [], occ ())], occ ())], occ ()) in
  check "an unregistered Peano chain does not fold"
    ((not (Numeral_literal.folds two)) && Numeral_literal.fold two == two
    && Numeral_literal.constructor_literal two = None);
  check "spine leaves it a construction" (Core_normalize.spine two = two && Core_normalize.canonical_application two);
  let conv = MLapp (MLglob (mono "nconv"), [two]) in
  check "a global no mapping names is no numeral converter"
    ((not (Numeral_literal.converter_folds conv)) && Numeral_literal.converter_literal (r "nconv") two = None);
  check "no constructor of an unregistered inductive is a registered digit"
    (Numeral_literal.registered_constructor "num.uint.type" zero = None)
