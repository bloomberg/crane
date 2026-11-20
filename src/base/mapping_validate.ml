(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** See [mapping_validate.mli]. *)

open Names
open Mapping_descriptor

let warn_unsafe =
  CWarnings.create ~name:"crane-mapping-unsafe"
    ~category:CWarnings.CoreCategories.extraction (fun (instance, what) ->
      Pp.(
        str "Typed mapping "
        ++ Printer.pr_global instance
        ++ str " uses " ++ str what ++ str "."
        ++ spc ()
        ++ strbrk
             "Crane does not see the structure of this C++ text: it cannot \
              place const or references around it and passes it exactly as \
              written.  Prefer a structured Crane.Cpp type or a canonical \
              physical parameter." ) )

(** {1 Template holes} *)

type hole =
  | Named of string * string  (** [%arg(x)], [%stored(x)], [%yield(x, e)] *)
  | Word of string  (** [%ret], [%result], [%scrut], [%value], [%view], ... *)
  | Numbered of string  (** [%tN], [%aN], [%tmpN], [%brN], [%bIaJ]: the family *)

let is_digit c = c >= '0' && c <= '9'
let is_lower c = c >= 'a' && c <= 'z'
let is_alnum c = is_digit c || is_lower c || (c >= 'A' && c <= 'Z') || c = '_'

let all_digits s = s <> "" && String.for_all is_digit s

let classify word =
  let n = String.length word in
  let prefix p =
    let k = String.length p in
    n > k && String.sub word 0 k = p && all_digits (String.sub word k (n - k))
  in
  match word with
  | "ret" | "result" | "scrut" | "value" | "view" | "elem" | "ty" | "n" ->
    Some (Word word)
  | _ when prefix "tmp" -> Some (Numbered "tmp")
  | _ when prefix "br" -> Some (Numbered "br")
  | _ when prefix "t" -> Some (Numbered "t")
  | _ when prefix "a" -> Some (Numbered "a")
  | _ when n >= 4 && word.[0] = 'b' && is_digit word.[1] -> (
    match String.index_opt word 'a' with
    | Some i
      when all_digits (String.sub word 1 (i - 1))
           && all_digits (String.sub word (i + 1) (n - i - 1)) ->
      Some (Numbered "b")
    | _ -> None )
  | _ -> None

(* The holes of a template, outside C++ comments and string and character
   literals.  A [%] not followed by a hole of the vocabulary is C++ text (a
   modulo, say) and is skipped. *)
let holes text =
  let n = String.length text in
  let rec skip_quoted q i =
    if i >= n then n
    else if text.[i] = '\\' then skip_quoted q (i + 2)
    else if text.[i] = q then i + 1
    else skip_quoted q (i + 1)
  in
  let rec skip_to s i =
    if i >= n then n
    else
      let k = String.length s in
      if i + k <= n && String.sub text i k = s then i + k else skip_to s (i + 1)
  in
  let rec go acc i =
    if i >= n then List.rev acc
    else
      match text.[i] with
      | '"' -> go acc (skip_quoted '"' (i + 1))
      | '\'' -> go acc (skip_quoted '\'' (i + 1))
      | '/' when i + 1 < n && text.[i + 1] = '/' -> go acc (skip_to "\n" i)
      | '/' when i + 1 < n && text.[i + 1] = '*' -> go acc (skip_to "*/" (i + 2))
      | '%' when i + 1 < n && is_lower text.[i + 1] ->
        let j = ref (i + 1) in
        while !j < n && is_alnum text.[!j] do incr j done;
        let word = String.sub text (i + 1) (!j - i - 1) in
        if
          !j < n
          && text.[!j] = '('
          && (word = "arg" || word = "stored" || word = "yield")
        then
          let close = try String.index_from text !j ')' with Not_found -> n in
          let inside = String.sub text (!j + 1) (max 0 (close - !j - 1)) in
          let name =
            match String.index_opt inside ',' with
            | Some k -> String.sub inside 0 k
            | None -> inside
          in
          go (Named (word, String.trim name) :: acc) (close + 1)
        else
          let acc = match classify word with Some h -> h :: acc | None -> acc in
          go acc !j
      | _ -> go acc (i + 1)
  in
  go [] 0

let pr_hole = function
  | Named (w, x) -> Printf.sprintf "%%%s(%s)" w x
  | Word w -> "%" ^ w
  | Numbered "tmp" -> "%tmpN"
  | Numbered "b" -> "%bIaJ"
  | Numbered f -> "%" ^ f ^ "N"

let family = function Named (w, _) -> w | Word w -> w | Numbered f -> f

(** {1 Errors} *)

let error ~what instance ~subject detail =
  CErrors.user_err
    Pp.(
      hov 0
        ( str "Invalid " ++ str what ++ str " "
        ++ Printer.pr_global instance
        ++ str " for" ++ spc () ++ subject ++ str ":" ++ spc () ++ detail ++ str "." ) )

let quote s = "\"" ^ s ^ "\""

(** {1 Type mappings} *)

let rec stored_names acc = function
  | Cpp.Stored_component s -> s :: acc
  | Cpp.Apply (_, args) ->
    List.fold_left
      (fun acc -> function Cpp.Type_arg t -> stored_names acc t | Cpp.Value_arg _ -> acc)
      acc args
  | Cpp.Pointer t | Cpp.Const t -> stored_names acc t
  | Cpp.Name _ | Cpp.Source_type _ | Cpp.Unsafe_verbatim _ -> acc

let rec has_verbatim = function
  | Cpp.Unsafe_verbatim _ -> true
  | Cpp.Apply (_, args) ->
    List.exists (function Cpp.Type_arg t -> has_verbatim t | Cpp.Value_arg _ -> false) args
  | Cpp.Pointer t | Cpp.Const t -> has_verbatim t
  | Cpp.Name _ | Cpp.Source_type _ | Cpp.Stored_component _ -> false

let ends_with c s =
  let s = String.trim s in
  s <> "" && s.[String.length s - 1] = c

let top_level_reference = function
  | Cpp.Unsafe_verbatim s -> ends_with '&' s
  | _ -> false

let rec raw_pointer = function
  | Cpp.Pointer _ -> true
  | Cpp.Const t -> raw_pointer t
  | Cpp.Unsafe_verbatim s -> ends_with '*' s
  | _ -> false

let duplicates names =
  let rec go seen = function
    | [] -> None
    | x :: rest -> if List.mem x seen then Some x else go (x :: seen) rest
  in
  go [] names

(* The inductive the source type reduces to, if any. *)
let family_of env sigma source =
  let t = Reductionops.whd_all env sigma source in
  match EConstr.kind sigma (fst (EConstr.decompose_app sigma t)) with
  | Constr.Ind (ind, _) -> Some ind
  | _ -> None

let constructor_arity env ((mind, i), j) =
  let mib = Environ.lookup_mind mind env in
  mib.Declarations.mind_packets.(i).Declarations.mind_consnrealargs.(j - 1)

let type_mapping env sigma ~instance ~source (m : type_mapping) =
  let subject = Printer.pr_econstr_env env sigma source in
  let fail detail = error ~what:"type mapping" instance ~subject detail in
  let failf fmt = Printf.ksprintf (fun s -> fail (Pp.strbrk s)) fmt in
  let names = List.map (fun c -> c.component_name) m.type_components in
  (match duplicates names with
  | Some x -> failf "component %s is declared more than once" (quote x)
  | None -> ());
  let known where x =
    if not (List.mem x names) then
      failf "%s names component %s, which is not declared in type_components" where
        (quote x)
  in
  let check_template where allowed text =
    List.iter
      (fun h ->
        if not (List.mem (family h) allowed) then
          failf "%s uses the template hole %s, which is not available there" where
            (pr_hole h);
        match h with Named ("stored", x) -> known where x | _ -> ())
      (holes text)
  in
  let check_construction where allowed = function
    | Expr e -> check_template where allowed e
    | With_body (i, b) ->
      check_template where allowed i;
      check_template where ("result" :: allowed) b
  in
  (* Canonical type. *)
  List.iter (known "type_cpp") (List.rev (stored_names [] m.type_cpp));
  if top_level_reference m.type_cpp then
    failf
      "the canonical type is a C++ reference; a canonical type is a value \
       type, and Crane adds references where a parameter needs one";
  if has_verbatim m.type_cpp then warn_unsafe (instance, "UnsafeVerbatim in type_cpp");
  (* Copy and access. *)
  (match m.type_copy with
  | Copy_components l -> List.iter (known "CopyComponents") l
  | _ -> ());
  let read_style_names = function
    | Read_by_components l -> List.iter (known "ReadByComponents") l
    | _ -> ()
  in
  (match m.type_access with
  | Read_only_value r | Mutable_value r -> read_style_names r
  | Explicit_access s ->
    let exact = function Exact_parameter _ -> true | _ -> false in
    if
      exact s.explicit_read
      || Option.cata exact false s.explicit_write
      || Option.cata exact false s.explicit_replace
    then warn_unsafe (instance, "ExactParameter in type_access")
  | Read_only_handle _ | Mutable_handle _ -> ());
  (* Views. *)
  let view_templates = ["stored"; "t"; "tmp"] in
  let check_view label v =
    List.iter (known (label ^ " view_cpp")) (List.rev (stored_names [] v.view_cpp));
    if top_level_reference v.view_cpp then
      failf "the %s view type is a C++ reference; a view is passed by value" label;
    if has_verbatim v.view_cpp then
      warn_unsafe (instance, "UnsafeVerbatim in the " ^ label ^ " view type");
    check_template (label ^ " view_from_canonical") ("value" :: view_templates)
      v.view_from_canonical;
    match v.view_escape with
    | Materialise_view k ->
      check_construction (label ^ " MaterialiseView") ("view" :: "ret" :: view_templates) k
    | Borrow_only -> ()
  in
  (match m.type_views with
  | No_views -> ()
  | Read_views r -> check_view "read" r
  | Read_write_views (r, w, conv) ->
    ( match m.type_access with
    | Read_only_value _ | Read_only_handle _ ->
      failf
        "ReadWriteViews declares a writable view, but the access model is \
         read-only; a writable view needs MutableValue, MutableHandle or an \
         ExplicitAccess with a write form"
    | Explicit_access {explicit_write = None; _} ->
      failf
        "ReadWriteViews declares a writable view, but the ExplicitAccess has \
         no write form"
    | Mutable_value _ | Mutable_handle _ | Explicit_access _ -> () );
    check_view "read" r;
    check_view "writable" w;
    check_template "read_from_write" ("view" :: view_templates) conv);
  (* Lifetime. *)
  (match m.type_lifetime with
  | Native_raii when raw_pointer m.type_cpp ->
    failf
      "the canonical type is a raw pointer, which owns nothing, but the \
       lifetime model is NativeRAII; use RegionOwned, ExternallyOwned or \
       ManualShared"
  | _ -> ());
  (* Constructors and numerals. *)
  let fam = family_of env sigma source in
  let pr_decl d = Pp.string_of_ppcmds (Mapping_decode.pr_declaration env d) in
  let member where (d : declaration) =
    match (d.reference, fam) with
    | GlobRef.ConstructRef ((ind, _) as k), Some fam when Ind.CanOrd.equal ind fam -> k
    | _, None ->
      failf "%s names %s, but the mapped type is not an inductive type" where (pr_decl d)
    | _ ->
      failf "%s names %s, which is not a constructor of the mapped type" where
        (pr_decl d)
  in
  let field where k n =
    let arity = constructor_arity env k in
    if n < 0 || n >= arity then
      failf "%s names field %d, but the constructor has %d field%s (numbered from 0)"
        where n arity
        (if arity = 1 then "" else "s")
  in
  List.iter
    (fun c ->
      match c.component_type with
      | Field_type (d, n) ->
        let where = "component " ^ quote c.component_name in
        field where (member where d) n
      | Known_type _ -> ())
    m.type_components;
  (match m.type_interface with
  | Abstract_interface -> ()
  | Algebraic_interface ctors ->
    let seen = ref [] in
    List.iter
      (fun c ->
        let where = "the constructor mapping " ^ pr_decl c.ctor_source in
        let k = member "AlgebraicInterface" c.ctor_source in
        if List.exists (Construct.CanOrd.equal k) !seen then
          failf "%s appears more than once in AlgebraicInterface"
            (pr_decl c.ctor_source);
        seen := k :: !seen;
        check_construction (where ^ " ctor_build") ["a"; "t"; "ret"; "stored"; "tmp"]
          c.ctor_build;
        Option.iter
          (fun v ->
            check_template (where ^ " case_test") ["scrut"; "t"; "stored"; "tmp"] v.case_test;
            List.iter
              (fun (n, p) ->
                field (where ^ " case_fields") k n;
                let (Owned_projection e | Canonical_borrow_projection e | Read_view_projection e) = p in
                check_template (where ^ " projection") ["scrut"; "t"; "stored"; "ret"; "tmp"] e)
              v.case_fields)
          c.ctor_view)
      ctors);
  (* The head of the type of field [n] of the constructor [k]: [`Self] for
     the constructor's own inductive, [`Other] for another inductive. *)
  let field_head (((mind, _) as ind, _) as k) n =
    let mib = Environ.lookup_mind mind env in
    let ty, _ = Typeops.type_of_global_in_context env (GlobRef.ConstructRef k) in
    let decls = List.rev (fst (Term.decompose_prod_decls ty)) in
    match List.nth_opt decls (mib.Declarations.mind_nparams + n) with
    | Some decl -> (
      match Constr.kind (fst (Constr.decompose_app_list (Context.Rel.Declaration.get_type decl))) with
      | Constr.Ind (ind', _) when Ind.CanOrd.equal ind ind' -> `Self
      | Constr.Ind _ -> `Other
      | _ -> `Neither )
    | None -> `Neither
  in
  Option.iter
    (fun s ->
      let seen = ref [] in
      List.iter
        (fun c ->
          let where = "the numeral case " ^ pr_decl c.numeral_constructor in
          let k = member where c.numeral_constructor in
          if List.exists (Construct.CanOrd.equal k) !seen then
            failf "%s: the constructor has more than one numeral case" where;
          seen := k :: !seen;
          match c.numeral_action with
          | Numeral_successor n | Numeral_double n | Numeral_double_plus_one n ->
            field where k n;
            if field_head k n <> `Self then
              failf "%s: field %d is not of the mapped type, so it cannot be the number this action builds on" where n
          | Numeral_identity n | Numeral_negate n ->
            field where k n;
            if field_head k n <> `Other then
              failf "%s: field %d is not of another inductive type, whose numeral this action reads" where n
          | Numeral_zero | Numeral_one -> ())
        s.numeral_cases;
      (* The emitter writes only validated digits and a sign between text
         that builds a numeric literal or a call of a named constructor. *)
      let allowed extra text =
        String.for_all
          (fun ch ->
            (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9') || String.contains extra ch)
          text
      in
      ( match s.numeral_emitter with
      | Integer_token (prefix, suffix) ->
        if not (allowed "_()<>:, +-" prefix && allowed "_()<>:, +-" suffix) then
          failf
            "the IntegerToken emitter's prefix or suffix contains a character              that does not build a numeric literal or a wrapping macro or cast"
      | Decimal_constructor callee ->
        if callee = "" || not (allowed "_:<>, " callee) then
          failf "the DecimalConstructor emitter's callee %s is not a qualified C++ name" (quote callee) );
      List.iter
        (fun (d : declaration) ->
          let ty, _ = Typeops.type_of_global_in_context env d.reference in
          let rec conclusion t =
            match Constr.kind t with Constr.Prod (_, _, b) | Constr.LetIn (_, _, _, b) -> conclusion b | _ -> t
          in
          match (Constr.kind (fst (Constr.decompose_app_list (conclusion ty))), fam) with
          | Constr.Ind (ind, _), Some fam when Ind.CanOrd.equal ind fam -> ()
          | _ -> failf "the numeral converter %s does not return the mapped type" (pr_decl d))
        s.numeral_converters)
    m.type_numerals

(** {1 Operation mappings} *)

type runtime_binder = {
  binder_name : string option;
  binder_mapping : type_mapping option Lazy.t;
}

type operation_context = {
  runtime_binders : runtime_binder list option;
  result_mapping : type_mapping option;
}

let no_context = {runtime_binders = None; result_mapping = None}

let pr_binders binders =
  String.concat ", " (List.map (fun b -> match b.binder_name with Some x -> x | None -> "_") binders)

let read_only = function
  | Read_only_value _ | Read_only_handle _ -> true
  | Mutable_value _ | Mutable_handle _ | Explicit_access _ -> false

let operation_mapping env ~instance ~(source : declaration) cx (m : operation_mapping) =
  let subject = Mapping_decode.pr_declaration env source in
  let fail detail = error ~what:"operation mapping" instance ~subject detail in
  let failf fmt = Printf.ksprintf (fun s -> fail (Pp.strbrk s)) fmt in
  let template_allowed = ["arg"; "stored"; "ret"; "t"; "tmp"] in
  let template_holes =
    match m.operation_cpp with
    | Expr e -> List.map (fun h -> (h, template_allowed)) (holes e)
    | With_body (i, b) ->
      List.map (fun h -> (h, template_allowed)) (holes i)
      @ List.map (fun h -> (h, "result" :: template_allowed)) (holes b)
  in
  List.iter
    (fun (h, allowed) ->
      if not (List.mem (family h) allowed) then
        failf "operation_cpp uses the template hole %s, which is not available in an operation template"
          (pr_hole h))
    template_holes;
  match m.operation_contract with
  | Opaque_operation -> ()
  | Pure_operation (args, result, facts) | Effectful_operation (args, result, facts) ->
    let pure = match m.operation_contract with Pure_operation _ -> true | _ -> false in
    let names = List.map (fun a -> a.argument_name) args in
    (match duplicates names with
    | Some x -> failf "argument %s is declared more than once" (quote x)
    | None -> ());
    (* Rule 19.6.2: one argument per retained runtime binder, in order. *)
    let bound =
      match cx.runtime_binders with
      | None -> []
      | Some binders ->
        let n = List.length binders and k = List.length args in
        if n <> k then
          failf
            "the contract declares %d argument%s (%s), but the operation has %d \
             retained runtime binder%s (%s) after Crane erases its type, proof, \
             type-class and Extraction Implicit parameters; declare one \
             argument per binder, in source order"
            k (if k = 1 then "" else "s") (String.concat ", " names) n
            (if n = 1 then "" else "s") (pr_binders binders);
        List.iter2
          (fun a b ->
            match b.binder_name with
            | Some x when x <> a.argument_name ->
              failf
                "argument %s is bound to the runtime binder %s; the arguments \
                 must name the retained runtime binders in source order (%s)"
                (quote a.argument_name) (quote x) (pr_binders binders)
            | _ -> ())
          args binders;
        List.combine names binders
    in
    let argument_mapping x =
      match List.assoc_opt x bound with Some b -> Lazy.force b.binder_mapping | None -> None
    in
    let use_of x = (List.find (fun a -> a.argument_name = x) args).argument_use in
    let declared where x =
      if not (List.mem x names) then
        failf "%s names argument %s, which is not declared in the contract" where (quote x)
    in
    List.iter
      (fun (h, _) ->
        match h with
        | Named ("arg", x) ->
          declared "operation_cpp" x;
          if use_of x = Ignore then
            failf "operation_cpp refers to %%arg(%s), but the argument is declared Ignore" x
        | _ -> ())
      template_holes;
    let impure what = if pure then failf "a PureOperation cannot %s" what in
    let path where p =
      if p.path_argument = "" then failf "%s has no owner argument" where;
      declared where p.path_argument;
      match argument_mapping p.path_argument with
      | Some tm ->
        let comps = List.map (fun c -> c.component_name) tm.type_components in
        List.iter
          (fun c ->
            if not (List.mem c comps) then
              failf "%s names component %s, which the type of argument %s does not declare"
                where (quote c) (quote p.path_argument))
          p.path_components
      | None -> ()
    in
    List.iter
      (fun a ->
        let x = quote a.argument_name in
        let tm = argument_mapping a.argument_name in
        match a.argument_use with
        | Write | Write_canonical ->
          impure ("write argument " ^ x);
          ( match tm with
          | Some tm when read_only tm.type_access ->
            failf "argument %s is written, but its type's access model is read-only" x
          | Some {type_access = Explicit_access {explicit_write = None; _}; _} ->
            failf "argument %s is written, but its type's ExplicitAccess has no write form" x
          | _ -> () )
        | Replace ->
          impure ("replace argument " ^ x);
          ( match tm with
          | Some tm when read_only tm.type_access ->
            failf "argument %s is replaced, but its type's access model is read-only" x
          | Some {type_access = Explicit_access {explicit_replace = None; _}; _} ->
            failf "argument %s is replaced, but its type's ExplicitAccess has no replace form" x
          | _ -> () )
        | Ignore | Read | Read_canonical | Take | Opaque_use -> ())
      args;
    (match result with
    | Return_value | Return_opaque -> ()
    | Return_borrowed (form, origin) -> (
      path "the borrowed result's origin" origin;
      match (form, cx.result_mapping) with
      | Read_view_borrow, Some {type_views = No_views; _} ->
        failf "the result is a ReadViewBorrow, but the result type declares no read view"
      | Writable_view_borrow, Some {type_views = No_views | Read_views _; _} ->
        failf
          "the result is a WritableViewBorrow, but the result type declares no \
           writable view"
      | _ -> () )
    | Return_same_identity x -> declared "ReturnSameIdentity" x
    | Return_fresh_identity inits ->
      impure "return a fresh identity";
      ( match cx.result_mapping with
      | Some {type_lifetime = Externally_owned; _} ->
        failf
          "the result is a fresh identity, but the result type is \
           ExternallyOwned, so Crane could not own it"
      | _ -> () );
      List.iter
        (fun i ->
          Option.iter (declared "ComponentInitialiser") i.initial_source_argument;
          match cx.result_mapping with
          | Some tm
            when not
                   (List.exists
                      (fun c -> c.component_name = i.initial_component)
                      tm.type_components) ->
            failf "ComponentInitialiser names component %s, which the result type does not declare"
              (quote i.initial_component)
          | _ -> ())
        inits);
    List.iter
      (function
        | Reads_component p -> path "ReadsComponent" p
        | Writes_component (p, s) ->
          impure "write a component (WritesComponent)";
          path "WritesComponent" p;
          Option.iter (declared "WritesComponent") s
        | Invalidates_element_borrows p -> path "InvalidatesElementBorrows" p
        | Invalidates_views p -> (
          path "InvalidatesViews" p;
          (* An argument whose views the operation invalidates (it may
             reallocate) cannot be given to it as a view (design 13.8). *)
          match (use_of p.path_argument, argument_mapping p.path_argument) with
          | Read, Some {type_views = Read_views _ | Read_write_views _; _} ->
            failf
              "argument %s is declared Read, so it is given as its type's read view, but \
               InvalidatesViews names it: an operation that invalidates views \
               cannot work through one; declare it ReadCanonical, WriteCanonical or Replace"
              (quote p.path_argument)
          | Write, Some {type_views = Read_write_views _; _} ->
            failf
              "argument %s is declared Write, so it is given as its type's writable view, but \
               InvalidatesViews names it: an operation that invalidates views \
               (a resize) cannot work through one; declare it WriteCanonical or Replace"
              (quote p.path_argument)
          | _ -> () )
        | Retains_argument (x, p) ->
          impure "retain an argument (RetainsArgument)";
          declared "RetainsArgument" x;
          path "RetainsArgument" p
        | Releases_identity x ->
          impure "release an identity (ReleasesIdentity)";
          declared "ReleasesIdentity" x
        | External_effect _ -> impure "have an external effect (ExternalEffect)")
      facts
