(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

module Needs = struct
  type t = {templates : string list; names : string list; defines : string list}

  let none = {templates = []; names = []; defines = []}
  let is_none n = n.templates = [] && n.names = [] && n.defines = []
  let union a b = {templates = a.templates @ b.templates; names = a.names @ b.names; defines = a.defines @ b.defines}
end

type spelling = Element_of of ModPath.t | Member_of of ModPath.t

type resolution = Unresolved | Resolved of Cpp_name.t
type module_ref = {path : ModPath.t; name : resolution}
type global_ref = {global : GlobRef.t; name : resolution}

type concept_ref = {module_type : ModPath.t; name : resolution}

type declared_module = {declares : ModPath.t; name : resolution}

let module_ref path = {path; name = Unresolved}
let global_ref global = {global; name = Unresolved}
let concept_ref module_type = {module_type; name = Unresolved}
let declared_module declares = {declares; name = Unresolved}

type template_param =
  | Typename of parameter
  | Constrained of {concept : concept_ref; args : module_ref list; param : module_ref}

and parameter = Type_variable of Id.t | Module_parameter of module_ref

type resolver = Cpp_resolution.frame -> Cpp_resolution.key -> Cpp_name.t

type declaration =
  | Declaration of {env : Common.env; settled : Cpp_erasure.settled}
  | Absorbed of {env : Common.env; settled : Cpp_erasure.settled}
  | Fields of {record : GlobRef.t; vars : Id.t list; fields : (string * Minicpp.cpp_type) list}
  | Modtype_concept of {path : ModPath.t; params : ModPath.t list; concept : Modtype_concept.t}
  | Global_alias of global_alias
  | Assertion of assertion
  | Module_alias of {name : declared_module; target : module_expr}
  | Functor_alias of {name : declared_module; functor_ : module_ref; params : (template_param * module_ref) list}
  | Derived_functor of {template : template_param list; name : declared_module; base : module_expr}

and module_expr = Module_named of module_ref | Applied of application

and application = {functor_ : module_ref; args : module_ref list}

and assertion = {concept : asserted; subject : subject}
and asserted = Of_module_type of concept_ref | Of_class of global_ref
and subject = Module of module_ref | Instance of {instance : global_ref; args : Minicpp.cpp_type list}

and global_alias =
  | Alias_of_type of {
      target : global_ref;
      definition : definition;
      tparams : (Minicpp.template_type * Id.t) list;
    }
  | Alias_of_module of module_ref

and definition = Cpp_resolution.definition = Enum_definition | Struct_definition | Alias_definition

type unprinted = {declaration : declaration; needs : Needs.t; names : Cpp_resolution.table}

type t =
  | Text of Pp.t
  | Decl of {text : Pp.t; needs : Needs.t}
  | Unprinted of unprinted
  | Elements of {source : ModPath.t; elements : t}
  | Seq of t list
  | Joined of t list
  | Top_level of t
  | Module of {module_ : ModPath.t; enclosure : enclosure; fields : t; members : t list}
  | Wrapper_struct of {name : string; module_ : ModPath.t; fields : t}
  | Concept_group of {position : concept_position; concepts : t list}
  | Declarations of Pp.t list

and enclosure = Struct of {head : struct_head; layout : layout} | Out_of_line | In_enclosing_scope
and struct_head = {template : template_param list; name : struct_name; base : base option}
and struct_name = Named of string | Module_struct of declared_module
and base = Of_itself of {template : string; type_args : Id.t list}
and layout = Block | One_line
and concept_position = Classes_ahead | Module_types_ahead | After_struct

let text d = Text d
let empty = Seq []

let rec concat sep = function
  | [] -> empty
  | [t] -> t
  | t :: rest -> Seq [t; Text (sep ()); concat sep rest]

(* A group of concepts as written: each on its own line, a blank line after
   the last, and in front of the first a line break if they are classes'
   concepts ahead of their module's struct, or a blank line if they follow
   it. *)
let laid_out position concepts =
  let lead =
    match position with
    | Classes_ahead -> [Text (Pp.fnl ())]
    | Module_types_ahead -> []
    | After_struct -> [Text Pp.(fnl () ++ fnl ())]
  in
  Seq (lead @ [concat Pp.fnl concepts; Text Pp.(fnl () ++ fnl ())])

let concept_group position = function [] -> empty | concepts -> Concept_group {position; concepts}

let resolved what = function
  | Resolved n -> Cpp_name.pp n
  | Unresolved -> invalid_arg ("Cpp_ast: " ^ what ^ " printed before it was resolved")

let pp_list pp l = Pp.(prlist_with_sep (fun () -> str ", ") pp l)
let pp_module_ref (m : module_ref) = resolved ("the module " ^ ModPath.to_string m.path) m.name

let pp_template_head = function
  | [] -> Pp.mt ()
  | params ->
    let param = function
      | Typename (Type_variable var) -> Pp.(str "typename " ++ Id.print var)
      | Typename (Module_parameter m) -> Pp.(str "typename " ++ pp_module_ref m)
      | Constrained {concept; args; param} ->
        Pp.(
          resolved ("the concept of " ^ ModPath.to_string concept.module_type) concept.name
          ++ (match args with [] -> mt () | args -> str "<" ++ pp_list pp_module_ref args ++ str ">")
          ++ str " " ++ pp_module_ref param)
    in
    Pp.(str "template<" ++ pp_list param params ++ str ">" ++ fnl ())

let pp_declared_module (m : declared_module) = resolved ("the declared name of " ^ ModPath.to_string m.declares) m.name

let pp_struct_head {template; name; base} =
  let name = match name with Named s -> Pp.str s | Module_struct m -> pp_declared_module m in
  let pp_base = function
    | Of_itself {template; type_args} ->
      let args = match type_args with [] -> Pp.mt () | vs -> Pp.(str "<" ++ pp_list Id.print vs ++ str ">") in
      Pp.(str template ++ str "<" ++ name ++ args ++ str ">")
  in
  Pp.(
    pp_template_head template ++ str "struct " ++ name
    ++ (match base with Some b -> str " : public " ++ pp_base b | None -> mt ())
    ++ str " {")
let decl ~needs text = Decl {text; needs}
let leaf ?(needs = Needs.none) declaration = Unprinted {declaration; needs; names = Cpp_resolution.unresolved}
let unprinted ~needs env settled = leaf ~needs (Declaration {env; settled})
let absorbed env settled = leaf (Absorbed {env; settled})
let fields ~needs ~record ~vars fields = leaf ~needs (Fields {record; vars; fields})
let modtype_concept ~path ~params concept = leaf (Modtype_concept {path; params; concept})
let global_alias a = leaf (Global_alias a)
let assertion a = leaf (Assertion a)
let module_alias mp target = leaf (Module_alias {name = declared_module mp; target})
let functor_alias mp functor_ params = leaf (Functor_alias {name = declared_module mp; functor_; params})
let derived_functor ~template mp base = leaf (Derived_functor {template; name = declared_module mp; base})
let wrapper_struct ~name ~module_ ~fields = Wrapper_struct {name; module_; fields}
let elements ~source elements = Elements {source; elements}
let seq l = Seq l

let rec is_empty = function
  | Text d -> Pp.ismt d
  | Decl {text; needs} -> Pp.ismt text && Needs.is_none needs
  | Unprinted _ -> false
  | Elements {elements; _} -> is_empty elements
  | Seq l | Joined l -> List.for_all is_empty l
  | Top_level _ -> false
  | Module {enclosure = Struct _; _} | Wrapper_struct _ -> false
  | Module {fields; members; _} -> members = [] && is_empty fields
  | Concept_group _ -> false
  | Declarations l -> l = []

let joined l = match List.filter (fun t -> not (is_empty t)) l with [] -> empty | [t] -> t | l -> Joined l
let top_level t = if is_empty t then t else Top_level t

type body = {body_module : ModPath.t; body_members : t list}

let module_body mp members = {body_module = mp; body_members = List.filter (fun t -> not (is_empty t)) members}
let body_is_empty b = b.body_members = []

let rec has_top_level = function
  | Text _ | Decl _ | Unprinted _ | Declarations _ -> false
  | Elements {elements; _} -> has_top_level elements
  | Top_level _ -> true
  | Seq l | Joined l -> List.exists has_top_level l
  | Module {fields; members; _} -> List.exists has_top_level (fields :: members)
  | Wrapper_struct {fields; _} -> has_top_level fields
  | Concept_group {concepts; _} -> List.exists has_top_level concepts

let module_ enclosure ?(fields = empty) b =
  ( match enclosure with
  | Struct _ when List.exists has_top_level (fields :: b.body_members) ->
    invalid_arg "Cpp_ast.module_: a chunk at namespace scope inside a struct"
  | Struct {layout = One_line; _} when not (is_empty fields && b.body_members = []) ->
    invalid_arg "Cpp_ast.module_: a struct laid out on one line with a body"
  | Struct _ | Out_of_line | In_enclosing_scope -> () );
  let t = Module {module_ = b.body_module; enclosure; fields; members = b.body_members} in
  if is_empty t then empty else t

let rec needs = function
  | Text _ | Declarations _ -> Needs.none
  | Decl {needs; _} | Unprinted {needs; _} -> needs
  | Elements {elements; _} -> needs elements
  | Seq l | Joined l -> List.fold_left (fun acc t -> Needs.union acc (needs t)) Needs.none l
  | Top_level t -> needs t
  | Module {fields; members; _} -> needs (Seq (fields :: members))
  | Wrapper_struct {fields; _} -> needs fields
  | Concept_group {concepts; _} -> needs (Seq concepts)

type declared = Declared of declaration | Struct_of of ModPath.t

let rec declared = function
  | Text _ | Decl _ | Declarations _ -> []
  | Unprinted {declaration; _} -> [Declared declaration]
  | Elements {elements = t; _} | Top_level t -> declared t
  | Seq l | Joined l | Concept_group {concepts = l; _} -> List.concat_map declared l
  | Module {module_; enclosure = Struct _; _} | Wrapper_struct {module_; _} -> [Struct_of module_]
  | Module {fields; members; enclosure = Out_of_line | In_enclosing_scope; _} ->
    List.concat_map declared (fields :: members)

let cut2 () = Pp.(brk (0, -100000) ++ brk (0, 0))

(* Whether the first text [t] writes opens a doc comment; a soft break, which
   may print as nothing, is no text.  Declarations scheduled in front of a
   chunk are not part of it: the break in front of a member was chosen by the
   member, before any was placed. *)
let starts_with_doc_comment t =
  let rec first_output = function
    | [] -> None
    | p :: rest -> (
      match Pp.repr p with
      | Ppcmd_empty | Ppcmd_print_break _ -> first_output rest
      | Ppcmd_string text -> Some (String.starts_with ~prefix:"///" text)
      | Ppcmd_glue parts -> (
        match first_output parts with Some _ as result -> result | None -> first_output rest )
      | Ppcmd_box (_, contents) | Ppcmd_tag (_, contents) -> (
        match first_output [contents] with Some _ as result -> result | None -> first_output rest )
      | Ppcmd_force_newline | Ppcmd_comment _ -> Some false )
  in
  let rec first = function
    | [] -> None
    | t :: rest -> (
      let inner =
        match t with
        | Text d | Decl {text = d; _} -> first_output [d]
        | Unprinted _ -> invalid_arg "Cpp_ast.starts_with_doc_comment: an unprinted declaration"
        | Elements {elements; _} -> first [elements]
        | Declarations _ -> None
        | Seq l | Joined l -> first l
        | Top_level t -> first [t]
        | Module {enclosure = Struct _; _} | Wrapper_struct _ -> Some false
        | Module {fields; members; _} -> first (fields :: members)
        | Concept_group {position; concepts} -> first [laid_out position concepts]
      in
      match inner with Some _ -> inner | None -> first rest )
  in
  match first [t] with Some result -> result | None -> false

(* Each two of [l] separated by a break, or by a newline where what follows
   opens with a doc comment: an unbroken [}///] or [;///] reads as a
   trailing comment, which the formatter cannot repair.  What follows is
   [following rest], the items after the break. *)
let rec join ~following = function
  | [] -> []
  | [t] -> [t]
  | t :: rest -> t :: Text (if starts_with_doc_comment (following rest) then Pp.fnl () else cut2 ()) :: join ~following rest

(* A module's members are read one at a time; a joined list as everything
   after the break. *)
let join_members = join ~following:List.hd
let join_items = join ~following:(fun rest -> Seq rest)

let rec to_pp = function
  | Text d -> d
  | Decl {text; _} -> text
  | Unprinted _ -> invalid_arg "Cpp_ast.to_pp: an unprinted declaration"
  | Elements {elements; _} -> to_pp elements
  | Seq l -> List.fold_left (fun acc t -> Pp.(acc ++ to_pp t)) (Pp.mt ()) l
  | Joined l -> to_pp (Seq (join_items l))
  | Top_level t -> to_pp t
  | Module {enclosure; fields; members; _} -> (
    let inside = to_pp (Seq (fields :: join_members members)) in
    match enclosure with
    | Struct {head; layout} ->
      Pp.(
        pp_struct_head head
        ++ (match layout with Block -> fnl () | One_line -> mt ())
        ++ inside
        ++ (if members = [] then mt () else fnl ())
        ++ str "};")
    | Out_of_line | In_enclosing_scope -> inside )
  | Wrapper_struct _ -> invalid_arg "Cpp_ast.to_pp: a wrapper struct whose body is not filled in"
  | Concept_group {position; concepts} -> to_pp (laid_out position concepts)
  | Declarations l -> Pp.(prlist_with_sep fnl (fun d -> d) l ++ cut2 ())

let rec wrapper_structs = function
  | Text _ | Decl _ | Unprinted _ | Declarations _ -> []
  | Elements {elements = t; _} | Top_level t -> wrapper_structs t
  | Seq l | Joined l | Concept_group {concepts = l; _} -> List.concat_map wrapper_structs l
  | Module {fields; members; _} -> List.concat_map wrapper_structs (fields :: members)
  | Wrapper_struct {name; fields; _} -> wrapper_structs fields @ [name]

let rec fill_wrappers bodies t =
  let fill = fill_wrappers bodies in
  match t with
  | Text _ | Decl _ | Unprinted _ | Declarations _ -> t
  | Elements e -> Elements {e with elements = fill e.elements}
  | Top_level t -> Top_level (fill t)
  | Seq l -> Seq (List.map fill l)
  | Joined l -> Joined (List.map fill l)
  | Concept_group g -> Concept_group {g with concepts = List.map fill g.concepts}
  | Module m -> Module {m with fields = fill m.fields; members = List.map fill m.members}
  | Wrapper_struct {name; module_ = wrapped; fields} -> (
    match List.assoc_opt name bodies with
    | Some b when ModPath.equal b.body_module wrapped ->
      module_ (Struct {head = {template = []; name = Named name; base = None}; layout = Block}) ~fields:(fill fields) b
    | Some _ -> invalid_arg ("Cpp_ast.fill_wrappers: the body given for " ^ name ^ " is another module's")
    | None -> invalid_arg ("Cpp_ast.fill_wrappers: no body for the wrapper struct " ^ name) )

type template = {name : string; homed : bool; holder : bool; declaration : Pp.t}
type forward = {struct_ : string; forward_declaration : Pp.t}
type translation_unit = {
  forward_declarations : Pp.t list;
  erased_aliases : t list;
  concept_prerequisites : t list;
  concepts : t list;
  hoisted_structs : t list;
  lifted_specs : t list;
  body : t;
  deferred_definitions : t list;
  deferred_members : t list;
  wrapper_bodies : (string * body) list;
}
type scheduled = {opening : Pp.t; body : t list}

let sections u =
  let non_empty = List.filter (fun t -> not (is_empty t)) in
  let groups sep l = match non_empty l with [] -> empty | l -> Seq [concat sep l; Text (cut2 ())] in
  let after_breaks l = Seq (List.concat_map (fun t -> [Text (cut2 ()); t]) (non_empty l)) in
  List.map top_level
    [ groups Pp.fnl u.erased_aliases;
      groups cut2 u.concept_prerequisites;
      groups cut2 u.concepts;
      groups cut2 u.hoisted_structs;
      groups cut2 u.lifted_specs;
      u.body;
      after_breaks u.deferred_definitions;
      (match non_empty u.deferred_members with [] -> empty | l -> Seq [Text (cut2 ()); concat cut2 l]) ]

(* The chunks are numbered in the order written, in both passes: a chunk at
   namespace scope and a member of a struct each take the next number. *)
let schedule ~templates ~forwards u =
  let u_sections = List.map (fill_wrappers u.wrapper_bodies) (sections u) in
  let template_slots = Hashtbl.create 16 and placed_in = Hashtbl.create 16 in
  let struct_slot = Hashtbl.create 16 and defined_in = Hashtbl.create 16 in
  let count = ref 0 in
  (* Where each template and constrained struct is first needed, from the
     innermost chunk at namespace scope [top], the innermost member [member]
     and the innermost module struct [scope] enclosing the declaration that
     needs it; and which structs each chunk at namespace scope defines,
     which a chunk returns.  A homed template is first needed once in each
     struct: a sibling's declaration is not in scope, and the name, a digest
     of the body, is the same in every struct writing the same text. *)
  let rec first_uses ~top ~member ~scope = function
    | Text _ | Declarations _ -> []
    | Seq l | Joined l | Concept_group {concepts = l; _} -> List.concat_map (first_uses ~top ~member ~scope) l
    | Elements {elements; _} -> first_uses ~top ~member ~scope elements
    | Top_level t ->
      incr count;
      let k = !count in
      let defined = first_uses ~top:(Some k) ~member ~scope t in
      Hashtbl.replace defined_in k defined;
      defined
    | Wrapper_struct _ -> invalid_arg "Cpp_ast.schedule: a wrapper struct whose body is not filled in"
    | Module {module_; enclosure; fields; members} ->
      let defined = first_uses ~top ~member ~scope fields in
      let scope = match enclosure with Struct _ -> Some module_ | Out_of_line | In_enclosing_scope -> scope in
      defined
      @ List.concat_map
          (fun t ->
            incr count;
            first_uses ~top ~member:(Some !count) ~scope t )
          members
    | Decl {needs; _} | Unprinted {needs; _} ->
      List.iter
        (fun name ->
          match List.find_opt (fun (a : template) -> String.equal a.name name) templates with
          | Some a -> (
            let in_, slot = if a.homed && Option.has_some member then (scope, member) else (None, top) in
            if not (Hashtbl.mem placed_in (name, in_)) then (
              Hashtbl.replace placed_in (name, in_) ();
              Hashtbl.add template_slots slot name ) )
          | None -> () )
        needs.templates;
      List.iter (fun name -> if not (Hashtbl.mem struct_slot name) then Hashtbl.replace struct_slot name top) needs.names;
      needs.defines
  in
  List.iter (fun t -> ignore (first_uses ~top:None ~member:None ~scope:None t)) u_sections;
  let templates_due k =
    let due = List.filter (fun (a : template) -> List.mem a.name (Hashtbl.find_all template_slots k)) templates in
    let holders, aliases = List.partition (fun (a : template) -> a.holder) due in
    List.map (fun (a : template) -> a.declaration) (holders @ aliases)
  in
  let forwards_due k =
    List.filter_map
      (fun f ->
        match Hashtbl.find_opt struct_slot f.struct_ with
        | Some (Some k') when k' = k && not (List.mem f.struct_ (Hashtbl.find defined_in k)) ->
          Some f.forward_declaration
        | _ -> None )
      forwards
  in
  let in_front due t = match due with [] -> t | l -> Seq [Declarations l; t] in
  count := 0;
  let rec placed = function
    | (Text _ | Decl _ | Unprinted _ | Declarations _) as t -> t
    | Seq l -> Seq (List.map placed l)
    | Joined l -> Joined (List.map placed l)
    | Concept_group g -> Concept_group {g with concepts = List.map placed g.concepts}
    | Elements e -> Elements {e with elements = placed e.elements}
    | Top_level t ->
      incr count;
      let k = !count in
      let due = forwards_due k @ templates_due (Some k) in
      in_front due (Top_level (placed t))
    | Module m ->
      let fields = placed m.fields in
      let members =
        List.map
          (fun t ->
            incr count;
            let due = templates_due (Some !count) in
            in_front due (placed t) )
          m.members
      in
      Module {m with fields; members}
    | Wrapper_struct _ -> invalid_arg "Cpp_ast.schedule: a wrapper struct whose body is not filled in"
  in
  let body = List.map placed u_sections in
  let prologue =
    match u.forward_declarations with [] -> Pp.mt () | l -> Pp.(prlist_with_sep fnl (fun d -> d) l ++ cut2 ())
  in
  let opening = match templates_due None with [] -> prologue | l -> Pp.(prologue ++ to_pp (Declarations l)) in
  {opening; body}

(* [t] with each declaration not yet printed replaced by [f] of it and how
   the innermost group or struct around it spells it, and the head of each
   struct by [head] of it and how what is around the struct spells it, if
   anything does. *)
let map_leaves ?(head = fun _ h -> h) f t =
  let rec map spelling = function
    | (Text _ | Decl _ | Declarations _) as t -> t
    | Unprinted u -> (
      match spelling with
      | Some spelling -> f spelling u
      | None -> invalid_arg "Cpp_ast: a declaration written where nothing says how it is spelled" )
    | Elements {source; elements} -> Elements {source; elements = map (Some (Element_of source)) elements}
    | Seq l -> Seq (List.map (map spelling) l)
    | Joined l -> Joined (List.map (map spelling) l)
    | Concept_group g -> Concept_group {g with concepts = List.map (map spelling) g.concepts}
    | Top_level t -> Top_level (map spelling t)
    | Module m ->
      let enclosure, inner =
        match m.enclosure with
        | Struct s -> (Struct {s with head = head spelling s.head}, Some (Member_of m.module_))
        | (Out_of_line | In_enclosing_scope) as e -> (e, None)
      in
      Module {m with enclosure; fields = map inner m.fields; members = List.map (map inner) m.members}
    | Wrapper_struct _ -> invalid_arg "Cpp_ast: a wrapper struct whose body is not filled in"
  in
  map None t

(* Each name written as [here] names it where it is written. *)
let resolve_module_ref here (m : module_ref) = {m with name = Resolved (here (Cpp_resolution.Module m.path))}
let resolve_declared_module here (m : declared_module) = {m with name = Resolved (here (Cpp_resolution.Module_declared m.declares))}

let resolve_template_param here = function
  | Typename (Type_variable _) as p -> p
  | Typename (Module_parameter m) -> Typename (Module_parameter (resolve_module_ref here m))
  | Constrained {concept; args; param} ->
    Constrained
      { concept = {concept with name = Resolved (here (Modtype_concept concept.module_type))};
        args = List.map (resolve_module_ref here) args;
        param = resolve_module_ref here param }

(* Whether a struct's head names anything resolving it names. *)
let head_names {template; name; base = _} =
  (match name with Named _ -> false | Module_struct _ -> true)
  || List.exists (function Typename (Type_variable _) -> false | Typename (Module_parameter _) | Constrained _ -> true) template

let resolve_head (resolve : spelling -> resolver) spelling h =
  match spelling with
  | _ when not (head_names h) -> h
  | None -> invalid_arg "Cpp_ast: a struct whose head names a module written where nothing says how it is spelled"
  | Some spelling ->
    let here = resolve spelling [] in
    { h with
      template = List.map (resolve_template_param here) h.template;
      name = (match h.name with Named _ as n -> n | Module_struct m -> Module_struct (resolve_declared_module here m)) }

let resolve_declaration (resolve : resolver) declaration =
  let here key = resolve [] key in
  let module_ref = resolve_module_ref here and template_param = resolve_template_param here in
  let global_ref key (g : global_ref) = {g with name = Resolved (here (key g.global))} in
  let concept : asserted -> asserted = function
    | Of_class g -> Of_class (global_ref (fun r -> Class_concept r) g)
    | Of_module_type c -> Of_module_type {c with name = Resolved (here (Modtype_concept c.module_type))}
  in
  let subject : subject -> subject = function
    | Module m -> Module (module_ref m)
    | Instance i -> Instance {i with instance = global_ref (fun r -> Global (Type, r)) i.instance}
  in
  let module_expr = function
    | Module_named m -> Module_named (module_ref m)
    | Applied {functor_; args} -> Applied {functor_ = module_ref functor_; args = List.map module_ref args}
  in
  match declaration with
  | Module_alias a -> Module_alias {name = resolve_declared_module here a.name; target = module_expr a.target}
  | Functor_alias a ->
    Functor_alias
      { name = resolve_declared_module here a.name;
        functor_ = module_ref a.functor_;
        params = List.map (fun (p, m) -> (template_param p, module_ref m)) a.params }
  | Derived_functor a ->
    Derived_functor
      { template = List.map template_param a.template;
        name = resolve_declared_module here a.name;
        base = module_expr a.base }
  | Assertion a -> Assertion {concept = concept a.concept; subject = subject a.subject}
  | Global_alias (Alias_of_module m) -> Global_alias (Alias_of_module (module_ref m))
  | Global_alias (Alias_of_type a) ->
    Global_alias (Alias_of_type {a with target = global_ref (fun r -> Definition (a.definition, r)) a.target})
  | Declaration _ | Absorbed _ | Fields _ | Modtype_concept _ -> declaration

let resolve_tree ~requested ~resolve t =
  map_leaves ~head:(resolve_head resolve)
    (fun spelling u ->
      let resolve = resolve spelling in
      Unprinted
        { u with
          declaration = resolve_declaration resolve u.declaration;
          names = Cpp_resolution.resolve resolve (requested u.declaration) } )
    t

let resolve ~requested ~resolve s = {s with body = List.map (resolve_tree ~requested ~resolve) s.body}

(* Every declaration is printed before any text is joined: whether a member
   opens a doc comment decides the break in front of it. *)
let print_tree ~write t = to_pp (map_leaves (fun spelling u -> Decl {text = write spelling u; needs = u.needs}) t)

let print ~write s = Pp.(s.opening ++ List.fold_left (fun acc t -> acc ++ print_tree ~write t) (mt ()) s.body)

