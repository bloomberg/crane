(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type t = Digest.t

(** A serialization of one structure.  Every constructor writes a distinct
    tag and every list its length, so two different trees cannot write the
    same text. *)
type writer = {
  buf : Buffer.t;
  holes : (int, int) Hashtbl.t;
  metas : (int, int) Hashtbl.t;
}

let writer () =
  { buf = Buffer.create 4096; holes = Hashtbl.create 8; metas = Hashtbl.create 8 }

let tag w s = Buffer.add_string w.buf s; Buffer.add_char w.buf ' '

let str w s =
  Buffer.add_string w.buf (string_of_int (String.length s));
  Buffer.add_char w.buf ':';
  Buffer.add_string w.buf s;
  Buffer.add_char w.buf ' '

let int w i = tag w (string_of_int i)
let bool w b = tag w (if b then "t" else "f")

let list w f l = int w (List.length l); List.iter f l
let array w f a = int w (Array.length a); Array.iter f a
let option w f = function None -> tag w "-" | Some x -> tag w "+"; f x

(** [first_occurrence tbl k] numbers [k] by the order keys were first seen. *)
let first_occurrence tbl k =
  match Hashtbl.find_opt tbl k with
  | Some n -> n
  | None ->
    let n = Hashtbl.length tbl in
    Hashtbl.add tbl k n;
    n

let id w x = str w (Id.to_string x)
let label w l = str w (Label.to_string l)
let kername w kn = str w (KerName.to_string kn)
let mutind w m = kername w (MutInd.user m)
let modpath w mp = str w (ModPath.to_string mp)
let mbid w b = str w (MBId.to_string b)

let globref w = function
  | GlobRef.VarRef v -> tag w "V"; id w v
  | ConstRef c -> tag w "C"; kername w (Constant.user c)
  | IndRef (m, i) -> tag w "I"; mutind w m; int w i
  | ConstructRef ((m, i), j) -> tag w "K"; mutind w m; int w i; int w j

let erasure_reason w = function
  | Core.Erasure_reason.Type_argument -> tag w "Erasure_reason.Type_argument"
  | Core.Erasure_reason.Proof -> tag w "Erasure_reason.Proof"
  | Core.Erasure_reason.Configured_implicit {entity = r; position = n} -> tag w "Erasure_reason.Configured_implicit"; globref w r; int w n

let argument w = function Core.Signature.Argument.Runtime -> tag w "Signature.Argument.Runtime" | Core.Signature.Argument.Erased k -> tag w "Signature.Argument.Erased"; erasure_reason w k

let binder_name w = function
  | Core.Binder_name.Anonymous -> tag w "Binder_name.Anonymous"
  | Core.Binder_name.Source x -> tag w "Binder_name.Source"; id w x
  | Core.Binder_name.Generated x -> tag w "Binder_name.Generated"; id w x

let scheme_id w s = globref w (Scheme.Id.owner s); int w (Scheme.Id.arity s)

let rec type_ w = function
  | Core.Type.Arrow {parameter = a; result = b} -> tag w "Type.Arrow"; type_ w a; type_ w b
  | Core.Type.Global_app {head = r; type_arguments = tys; index_arguments = args} ->
    tag w "Type.Global_app"; globref w r; list w (type_ w) tys; list w (expr w) args
  | Core.Type.Variable {rigidity; variable = i} ->
    tag w (match rigidity with Core.Type.Rigidity.Schematic -> "Type.Variable" | Core.Type.Rigidity.Rigid -> "Type.Variable!"); int w i
  | Core.Type.Variable_app {head = i; arguments = tys} -> tag w "Type.Variable_app"; int w i; list w (type_ w) tys
  | Core.Type.Meta {contents = Some t; _} -> type_ w t
  | Core.Type.Meta {id = m; contents = None} -> tag w "Type.Meta"; int w (first_occurrence w.metas m)
  | Core.Type.Hole h -> tag w "Type.Hole"; int w (first_occurrence w.holes h)
  | Core.Type.Open o -> tag w "Type.Open"; int w (first_occurrence w.metas (Core.Open.id o))
  | Core.Type.Erased k -> tag w "Type.Erased"; erasure_reason w k
  | Core.Type.Unknown -> tag w "Type.Unknown"
  | Core.Type.Axiom -> tag w "Type.Axiom"
  | Core.Type.String -> tag w "Type.String"

and expr w = function
  | Core.Expr.Bound_variable {index = i; _} -> tag w "Expr.Bound_variable"; int w i
  | Core.Expr.Apply {callee = f; arguments = args} -> tag w "Expr.Apply"; expr w f; list w (expr w) args
  | Core.Expr.Lambda {parameter = x; parameter_type = ty; body = b} -> tag w "Expr.Lambda"; binder_name w x; type_ w ty; expr w b
  | Core.Expr.Let {binder = x; binder_type = ty; value = a; body = b; _} ->
    tag w "Expr.Let"; binder_name w x; type_ w ty; expr w a; expr w b
  | Core.Expr.Global u -> tag w "Expr.Global"; global_use w u
  | Core.Expr.Construct {result_type = ty; constructor = r; arguments = args; _} ->
    tag w "Expr.Construct"; type_ w ty; globref w r; list w (expr w) args
  | Core.Expr.Tuple args -> tag w "Expr.Tuple"; list w (expr w) args
  | Core.Expr.Match {scrutinee_type = ty; scrutinee = a; branches = brs; _} -> tag w "Expr.Match"; type_ w ty; expr w a; array w (branch w) brs
  | Core.Expr.Fixpoint {selected = i; functions = ids; bodies; _} -> tag w "Expr.Fixpoint"; fix w i ids bodies
  | Core.Expr.Cofixpoint {selected = i; functions = ids; bodies; _} -> tag w "Expr.Cofixpoint"; fix w i ids bodies
  | Core.Expr.Runtime_error s -> tag w "Expr.Runtime_error"; str w s
  | Core.Expr.Erased_value k -> tag w "Expr.Erased_value"; erasure_reason w k
  | Core.Expr.Axiom_value s -> tag w "Expr.Axiom_value"; str w s
  | Core.Expr.Coerce {source_type = from; target_type = into; value = a; _} -> tag w "Expr.Coerce"; type_ w from; type_ w into; expr w a
  | Core.Expr.Boxed_value {value = a; _} -> tag w "Expr.Boxed_value"; expr w a
  | Core.Expr.Lambda_group_barrier {value = a; _} -> tag w "Expr.Lambda_group_barrier"; expr w a
  | Core.Expr.UInt63 n -> tag w "Expr.UInt63"; str w (Uint63.to_string n)
  | Core.Expr.Float64 f -> tag w "Expr.Float64"; str w (Float64.to_hex_string f)
  | Core.Expr.String s -> tag w "Expr.String"; str w (Pstring.to_string s)
  | Core.Expr.Persistent_array {elements = xs; default = d} -> tag w "Expr.Persistent_array"; array w (expr w) xs; expr w d
  | Core.Expr.Numeral {inductive = r; value = n} -> tag w "Expr.Numeral"; globref w r; str w (Z.to_string n)

and fix w i ids bodies =
  int w i;
  array w (fun (x, ty) -> id w x; type_ w ty) ids;
  array w (expr w) bodies

and branch w {Core.Match.Branch.binders; result_type; pattern = pat; body} =
  list w (fun (x, t) -> binder_name w x; type_ w t) binders;
  type_ w result_type; pattern w pat; expr w body

and pattern w = function
  | Core.Pattern.Constructor {constructor = r; fields = ps} -> tag w "Pattern.Constructor"; globref w r; list w (pattern w) ps
  | Core.Pattern.Tuple ps -> tag w "Pattern.Tuple"; list w (pattern w) ps
  | Core.Pattern.Bound_variable i -> tag w "Pattern.Bound_variable"; int w i
  | Core.Pattern.Wildcard -> tag w "Pattern.Wildcard"

and global_use w u =
  globref w (Core.Global_use.callee u);
  match Core.Global_use.instantiation u with
  | None -> tag w "mono"
  | Some inst ->
    tag w "poly";
    scheme_id w (Scheme.Instantiation.scheme inst);
    Scheme.Instantiation.fold
      (fun v (s : Core.Type.t Scheme.slot) () ->
        int w (Scheme.Var.ordinal v);
        ( match s.solution with
        | Identity -> tag w "identity"
        | Type t -> tag w "type"; type_ w t );
        match s.source with
        | Not_written -> tag w "unwritten"
        | Written {binder; observed} ->
          tag w "written";
          int w (Scheme.Binder.position binder);
          option w (type_ w) observed )
      inst ()

let field w {Core.Record.Field.projection = r; type_ = ty} = option w (globref w) r; type_ w ty

let kind w = function
  | Core.Inductive.Kind.Coinductive -> tag w "Kind.Coinductive"
  | Core.Inductive.Kind.Inductive -> tag w "Kind.Inductive"
  | Core.Inductive.Kind.Record fs -> tag w "Kind.Record"; list w (field w) fs
  | Core.Inductive.Kind.Type_class fs -> tag w "Kind.Type_class"; list w (field w) fs

let packet w (p : Core.Inductive.Packet.t) =
  id w p.name;
  array w (id w) p.constructor_names;
  bool w p.logical;
  list w (argument w) p.signature;
  list w (id w) p.type_variables;
  array w (list w (type_ w)) p.constructor_argument_types;
  array w (list w (option w (id w))) p.constructor_argument_names

let inductive w (ind : Core.Inductive.t) =
  kind w ind.kind;
  int w ind.parameter_count;
  array w (packet w) ind.packets;
  match ind.equivalence with
  | Core.Inductive.Equivalence.Distinct -> tag w "Equivalence.Distinct"
  | Core.Inductive.Equivalence.Equivalent_to kn -> tag w "Equivalence.Equivalent_to"; kername w kn
  | Core.Inductive.Equivalence.Equivalent_in_renamed_module s -> tag w "Equivalence.Equivalent_in_renamed_module"; str w s

let definition w (d : Core.Recursion.Definition.t) =
  globref w d.entity; expr w d.body; type_ w d.type_

let declaration w = function
  | Core.Decl.Inductive {entity = m; definition = ind} -> tag w "Decl.Inductive"; mutind w m; inductive w ind
  | Core.Decl.Type_alias {entity = r; parameters = vars; body = ty} -> tag w "Decl.Type_alias"; globref w r; list w (id w) vars; type_ w ty
  | Core.Decl.Value {entity = r; body = a; type_ = ty} -> tag w "Decl.Value"; globref w r; expr w a; type_ w ty
  | Core.Decl.Recursive_group fds -> tag w "Decl.Recursive_group"; list w (definition w) (Core.Nonempty.to_list fds)

let signature_declaration w = function
  | Core.Signature.Declaration.Inductive {entity = m; definition = ind} -> tag w "Signature.Declaration.Inductive"; mutind w m; inductive w ind
  | Core.Signature.Declaration.Type {entity = r; parameters = vars; body = ty} ->
    tag w "Signature.Declaration.Type"; globref w r; list w (id w) vars; option w (type_ w) ty
  | Core.Signature.Declaration.Value {entity = r; body = a; type_ = ty} -> tag w "Signature.Declaration.Value"; globref w r; expr w a; type_ w ty

let rec module_type w = function
  | Core.Module.Type.Path mp -> tag w "Module.Type.Path"; modpath w mp
  | Core.Module.Type.Functor {parameter = b; parameter_type = a; result = r} -> tag w "Module.Type.Functor"; mbid w b; module_type w a; module_type w r
  | Core.Module.Type.Signature {path = mp; items = sg} -> tag w "Module.Type.Signature"; modpath w mp; list w (signature_item w) sg
  | Core.Module.Type.Refined {base = mt; refinement = wd} -> tag w "Module.Type.Refined"; module_type w mt; refinement w wd

and signature_item w (l, sp) =
  label w l;
  match sp with
  | Core.Module.Signature_item.Declaration s -> tag w "Module.Signature_item.Declaration"; signature_declaration w s
  | Core.Module.Signature_item.Module mt -> tag w "Module.Signature_item.Module"; module_type w mt
  | Core.Module.Signature_item.Module_type mt -> tag w "Module.Signature_item.Module_type"; module_type w mt

and refinement w = function
  | Core.Module.Refinement.Type_equation {path; parameters = vars; definition = ty} ->
    tag w "Module.Refinement.Type_equation"; list w (id w) path; list w (id w) vars; type_ w ty
  | Core.Module.Refinement.Module_equation {path; definition = mp} -> tag w "Module.Refinement.Module_equation"; list w (id w) path; modpath w mp

let rec structure_item w (l, se) =
  label w l;
  match se with
  | Core.Module.Structure_item.Declaration d -> tag w "Module.Structure_item.Declaration"; declaration w d
  | Core.Module.Structure_item.Module m -> tag w "Module.Structure_item.Module"; module_expr w m.expr; module_type w m.type_
  | Core.Module.Structure_item.Module_type mt -> tag w "Module.Structure_item.Module_type"; module_type w mt

and module_expr w = function
  | Core.Module.Expr.Path mp -> tag w "Module.Expr.Path"; modpath w mp
  | Core.Module.Expr.Functor {parameter = b; parameter_type = mt; body = me} -> tag w "Module.Expr.Functor"; mbid w b; module_type w mt; module_expr w me
  | Core.Module.Expr.Structure {path = mp; items = sel} -> tag w "Module.Expr.Structure"; modpath w mp; list w (structure_item w) sel
  | Core.Module.Expr.Apply {functor_ = f; argument = x} -> tag w "Module.Expr.Apply"; module_expr w f; module_expr w x

let digest write x =
  let w = writer () in
  write w x;
  Digest.string (Buffer.contents w.buf)

let structure =
  digest (fun w s -> list w (fun (mp, sel) -> modpath w mp; list w (structure_item w) sel) s)

let elements s =
  List.concat_map
    (fun (_, sel) -> List.map (fun ((l, _) as e) -> (l, digest structure_item e)) sel)
    s

let decl = digest declaration
let equal = Digest.equal
let to_hex = Digest.to_hex
