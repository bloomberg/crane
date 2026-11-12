(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* The constructor manifest of MiniCpp: what every constructor minicpp.mli
   declares becomes in CppIR.

   Each constructor is classified exactly once:

   - [rename target]: it becomes the CppIR constructor [target], at both
     phases;
   - [lowered target obligation]: it becomes [target], which exists only in
     CppIR.Lowered -- a resolved program cannot hold it -- and resolution
     discharges it as [obligation];
   - [dead why]: nothing produces it -- it occurs only in patterns, or in
     rebuilding a value that already holds it -- so CppIR has no constructor
     for it;
   - [not_syntax why]: it is not part of a declaration's syntax, so CppIR
     has no constructor for it.

   Lowered-only and dead were measured as well as read: across the test
   corpus under CRANE_CHECK_IR, no finished declaration holds one.

   A target is written by its public path ([Expr.Call], [Expr.Literal.String],
   [Inductive.Kind.Sum]) and is checked against src/cpp_ir: the family file
   that re-exports the grammar module, and the grammar module that declares
   the constructor.  A lowered-only target must be declared at [lowered]; a
   renamed one must not be.

   The test fails on a MiniCpp constructor with no entry, an entry naming a
   constructor MiniCpp no longer declares, or a target CppIR does not
   declare as the entry says. *)

type classification =
  | Rename of string
  | Lowered of string * string
  | Dead of string
  | Not_syntax of string

let rename t = Rename t
let lowered t obligation = Lowered (t, obligation)
let dead why = Dead why
let no_producer = dead "no constructing site"

let manifest : (string * classification) list =
  [ (* How an inductive is written: name resolution's classification, not
       part of a declaration (nothing in a finished declaration holds it). *)
    ("IK_Standard", rename "Inductive.Kind.Sum");
    ("IK_Enum", rename "Inductive.Kind.Enum");
    ("IK_Record", rename "Inductive.Kind.Record");
    ("IK_Eponymous", rename "Inductive.Kind.Eponymous_record");
    ("IK_TypeClass", rename "Inductive.Kind.Type_class");
    ("VPublic", rename "Field.Visibility.Public");
    ("VPrivate", rename "Field.Visibility.Private");
    ("STypes", rename "Field.Section.Types");
    ("SData", rename "Field.Section.Data");
    ("SCreators", rename "Field.Section.Creators");
    ("SManipulators", rename "Field.Section.Manipulators");
    ("SAccessors", rename "Field.Section.Accessors");
    ("SNoTag", rename "Field.Section.Untagged");
    ("Immediate", lowered "Expr.Capture.Runs_in_place" "Undecided_capture");
    ("Closure", lowered "Expr.Capture.Stored" "Undecided_capture");
    ("Written", rename "Expr.Capture.Written");
    ("Captures_nothing", rename "Expr.Written_capture.Nothing");
    ("By_reference", rename "Expr.Written_capture.By_reference");
    ("By_copy", rename "Expr.Written_capture.By_copy");
    ("Inline_variant", rename "Type.Variant_storage.Inline");
    ("Shared_variant", rename "Type.Variant_storage.Shared");
    ("Lvalue", rename "Type.Reference_kind.Lvalue");
    ("Forwarding", rename "Type.Reference_kind.Forwarding");
    ("Inline_identity", rename "Foreign.Identity");
    ("Inline_pair_projection", rename "Foreign.Pair_projection");
    ("Inline_other", rename "Foreign.Other");
    ("Block_iife", rename "Foreign.Block");
    ("Bare_callee", rename "Foreign.Bare_callee");
    ("Templated", rename "Foreign.Templated");
    ("Ek_type", rename "Type.Erased_kind.Type");
    ("Ek_prop", rename "Type.Erased_kind.Proof");
    ("Ek_implicit", rename "Type.Erased_kind.Implicit");
    ("Undecided", lowered "Decl.Constexpr.Undecided" "Undecided_constexpr");
    ("Eligible", rename "Decl.Constexpr.Eligible");
    ("Ineligible", rename "Decl.Constexpr.Ineligible");
    ("Tv_index", rename "Type.Type_variable.Index");
    ("Tv_named", rename "Type.Type_variable.Named");
    ("Tvar", rename "Type.Variable");
    ("Tinstance", rename "Type.Instance");
    ("Tpromoted", rename "Type.Promoted_member");
    ("Tid", rename "Type.Named");
    ("Tid_external", rename "Type.External");
    ("Tglob", rename "Type.Entity_application");
    ("Tfun", rename "Type.Function");
    ("Tconst", rename "Type.Const");
    ("Tnamespace", rename "Type.In_namespace");
    ("Tqualified", rename "Type.Member");
    ("Tapply", rename "Type.Apply");
    ("Tref", rename "Type.Reference");
    ("Terased", rename "Type.Erased");
    ("Tptr", rename "Type.Pointer");
    ("Tvariant", rename "Type.Variant");
    ("Tshared_ptr", rename "Type.Shared_pointer");
    ("Tvoid", rename "Type.Void");
    ("Tunresolved", lowered "Type.Obligation" "Unresolved_type");
    ("Tany", rename "Type.Any");
    ("Ttyctor", rename "Type.Type_constructor");
    ("Topaque", lowered "Type.Obligation" "Opaque_type");
    ("Tauto", rename "Type.Auto");
    ("Tdecay", rename "Type.Decay");
    ("Tnondeduced", rename "Type.Non_deduced");
    ("Trebind", rename "Type.Rebind");
    (* The parameter of a carrier's alias template: written in resolved
       declarations, so a type, not an obligation. *)
    ("Thole", rename "Type.Carrier_parameter");
    ("Texpr_type", rename "Type.Type_of");
    ("Tdecltype_auto", rename "Type.Decltype_auto");
    ("Tforeign", rename "Type.Foreign");
    ("Declare", rename "Stmt.Binding.Declare");
    ("Existing", rename "Stmt.Binding.Existing");
    ("Declare_static", rename "Stmt.Binding.Declare_static");
    ("Tt_convertible", rename "Type.Type_test.Convertible");
    ("Sreturn", rename "Stmt.Return");
    ("Sdecl", rename "Stmt.Declare");
    ("Sasgn", rename "Stmt.Bind_variable");
    ("Sexpr", rename "Stmt.Expression");
    ("Scustom_case", rename "Stmt.Custom_match");
    ("Sthrow", rename "Stmt.Throw");
    ("Sswitch", rename "Stmt.Switch");
    ("Sassert", rename "Stmt.Assert");
    ("Sif", rename "Stmt.If");
    ("Sif_constexpr", rename "Stmt.If_constexpr");
    ("Sif_decl", rename "Stmt.If_declaration");
    ("Sraw", rename "Stmt.Foreign_text");
    ("Scomment", rename "Stmt.Comment");
    ("Sstruct_def", rename "Stmt.Local_struct");
    ("Susing", rename "Stmt.Local_type_alias");
    ("Sbind", rename "Stmt.Structured_binding");
    ("Sdecl_init", rename "Stmt.Declare_value_initialized");
    ("Sassign_expr", rename "Stmt.Assign");
    ("Sfor_range", rename "Stmt.For_range");
    ("Swhile", rename "Stmt.While");
    ("Sblock", rename "Stmt.Block");
    ("Scontinue", rename "Stmt.Continue");
    ("Sbreak", rename "Stmt.Break");
    ("Sblock_custom", lowered "Stmt.Foreign_block" "Uninstantiated_mapping");
    ("Smatch", rename "Stmt.Match");
    ("Pchecked", rename "Stmt.Precondition.Checked");
    ("Pstated", rename "Stmt.Precondition.Stated");
    ("Beq", rename "Binary_operator.Equal");
    ("Bneq", rename "Binary_operator.Not_equal");
    ("Band", rename "Binary_operator.And");
    ("Bor", rename "Binary_operator.Or");
    ("Bassign", rename "Binary_operator.Assign");
    ("Unot", rename "Unary_operator.Not");
    ("Uaddr", rename "Unary_operator.Address_of");
    ("Alloc_heap", rename "Expr.Allocation.Heap");
    ("Alloc_arena_scoped", rename "Expr.Allocation.Arena_scoped");
    ("Alloc_reusing", rename "Expr.Allocation.Reusing");
    ("Boxed_whole", rename "Expr.Erase_shape.Boxed_whole");
    ("At_signature", rename "Expr.Erase_shape.At_signature");
    ("Ryields", rename "Expr.Call.Yields");
    ("Ropaque", rename "Expr.Call.Untyped");
    ("Ptypes", rename "Expr.Call.Types");
    ("Punknown", rename "Expr.Call.Unknown");
    ("Adot", rename "Expr.Access.Dot");
    ("Aarrow", rename "Expr.Access.Arrow");
    ("CPPvar", rename "Expr.Local");
    ("CPPglob", rename "Expr.Entity");
    ("CPPnamespace", no_producer);
    ("CPPfun_call", rename "Expr.Call");
    ("CPPconverting_ctor", rename "Expr.Converting_construct");
    ("CPPbox", rename "Expr.Box");
    ("CPPderef", rename "Expr.Dereference");
    ("CPPmove", rename "Expr.Move");
    ("CPPforward", rename "Expr.Forward");
    ("CPPlambda", rename "Expr.Lambda");
    ("CPPsuspend", lowered "Expr.Suspend" "Unlowered_qualifier");
    ("CPPalloc", rename "Expr.Allocate");
    ("CPPstructmk", no_producer);
    ("CPPstruct", rename "Expr.Aggregate");
    ("CPPstruct_id", rename "Expr.Local_aggregate");
    ("CPPget", rename "Expr.Member");
    ("CPPget'", rename "Expr.Project");
    ("CPPstring", rename "Expr.Literal.String");
    ("CPPuint", rename "Expr.Literal.Uint63");
    ("CPPfloat", rename "Expr.Literal.Float");
    ("CPPparray", rename "Expr.Persistent_array");
    ("CPPrequires", rename "Expr.Requires");
    ("CPPconcept_app", rename "Expr.Concept_application");
    ("CPPnew", no_producer);
    ("CPPshared_ptr_ctor", no_producer);
    ("CPPthis", rename "Expr.This");
    ("CPPshared_from_this", rename "Expr.Shared_from_this");
    ("CPPaccess", rename "Expr.Access");
    ("CPPaccess_call", rename "Expr.Access_call");
    ("CPPmethod_call", rename "Expr.Method_call");
    ("CPPmethod_value", rename "Expr.Method_value");
    ("CPPprojection", rename "Expr.Projection");
    ("CPPprojection_value", rename "Expr.Projection_value");
    ("CPPscope", rename "Expr.Scope");
    ("CPPqualified_t", rename "Expr.Type_member");
    ("CPPconvertible_to", rename "Expr.Convertible_to");
    ("CPPabort", rename "Expr.Abort");
    ("CPPenum_val", rename "Expr.Enum_value");
    ("CPPnullptr", rename "Expr.Literal.Null_pointer");
    ("CPPin_place", rename "Expr.In_place");
    ("CPPin_place_index", rename "Expr.In_place_index");
    ("CPPbraced", rename "Expr.Braced");
    ("CPPstd_get", rename "Expr.Variant_get");
    ("CPPstd_holds_alternative", rename "Expr.Holds_alternative");
    ("CPPdeclval", rename "Expr.Declval");
    ("CPPtype_name", rename "Expr.Type_name");
    ("CPPnumeral", rename "Expr.Numeral");
    ("CPPraw", rename "Expr.Foreign_text");
    ("CPPrt", rename "Expr.Runtime");
    ("CPPbinop", rename "Expr.Binary");
    ("CPPcond", rename "Expr.Conditional");
    ("CPPbool", rename "Expr.Literal.Bool");
    ("CPPint", rename "Expr.Literal.Int");
    ("CPPunop", rename "Expr.Unary");
    ("CPPany_cast", rename "Expr.Any_cast");
    ("CPPany_cast_tolerant", rename "Expr.Tolerant_any_cast");
    ("CPPunbox", rename "Expr.Unbox");
    ("CPPconvert", rename "Expr.Convert");
    ("CPPerase_fn", rename "Expr.Erase_callable");
    ("CPPerased_call", rename "Expr.Erased_call");
    ("CPPtolerant_call", rename "Expr.Tolerant_call");
    ("CPPfn_value", rename "Expr.Function_value");
    ("CPPcontainer_cast", rename "Expr.Container_cast");
    ("CPPstd_get_if", rename "Expr.Variant_get_if");
    ("CPPforeign", rename "Expr.Foreign");
    ("Self_passing", rename "Expr.Local_fixpoint.Self_passing");
    ("Knot", rename "Expr.Local_fixpoint.Knot");
    ("Lowered", rename "Expr.Local_fixpoint.Lowered");
    ("TTtypename", rename "Template.Parameter_kind.Typename");
    ("TTtypename_default", rename "Template.Parameter_kind.Typename_default");
    ("TTtemplate", rename "Template.Parameter_kind.Template");
    ("TTfun", lowered "Template.Parameter_kind.Callable_declared" "Unsettled_callable");
    ("TTinvocable", rename "Template.Parameter_kind.Invocable");
    ("TTconcept", rename "Template.Parameter_kind.Concept");
    ("Mutable_lvalue", rename "Template.Value_category.Mutable_lvalue");
    ("Const_lvalue", rename "Template.Value_category.Const_lvalue");
    ("Xvalue", rename "Template.Value_category.Xvalue");
    ("Prvalue", rename "Template.Value_category.Prvalue");
    ("Fvar", rename "Field.Data");
    ("Fvar'", rename "Field.Entity_data");
    ("Fmethod", rename "Field.Method");
    ("Fconstructor", rename "Field.Constructor");
    ("Fdestructor", rename "Field.Destructor");
    ("Fnested_struct", rename "Field.Nested_struct");
    ("Fdeferred_struct", rename "Field.Deferred_struct");
    ("Fnested_using", rename "Field.Nested_type_alias");
    ("Fmember_decl", rename "Field.Out_of_line_declaration");
    ("Fdeleted_ctor", rename "Field.Deleted_default_constructor");
    ("Fdefaulted_special_members", rename "Field.Defaulted_special_members");
    ("OLmethod", rename "Field.Out_of_line.Method");
    ("OLdestructor", rename "Field.Out_of_line.Destructor");
    ("Static", rename "Field.Receiver.Static");
    ("Instance", rename "Field.Receiver.Instance");
    ("Rq_any", rename "Field.Receiver.Any");
    ("Rq_lvalue", rename "Field.Receiver.Lvalue");
    ("Rq_rvalue", rename "Field.Receiver.Rvalue");
    ("Mp_text", rename "Stmt.Custom_match.Text");
    ("Mp_scrutinee", rename "Stmt.Custom_match.Scrutinee");
    ("Mp_matched_type", rename "Stmt.Custom_match.Matched_type");
    ("Mp_type_arg", rename "Stmt.Custom_match.Type_argument");
    ("Mp_branch", rename "Stmt.Custom_match.Branch");
    ("Mp_binder", rename "Stmt.Custom_match.Binder");
    ("Mp_binder_type", rename "Stmt.Custom_match.Binder_type");
    ("Scrut_owned", rename "Stmt.Custom_match.Owned");
    ("Scrut_borrowed", rename "Stmt.Custom_match.Borrowed");
    ("Unbox_to", rename "Expr.Unbox.To");
    ("Unbox_or_keep", rename "Expr.Unbox.Or_keep");
    ("Unbox_list", rename "Expr.Unbox.List");
    ("Fp_text", rename "Foreign.Text");
    ("Fp_type", rename "Foreign.Type_argument");
    ("Fp_element", rename "Foreign.Element");
    ("Fp_value", rename "Foreign.Value");
    ("Fp_yields", rename "Foreign.Yields");
    ("Fp_result", rename "Foreign.Result");
    ("Fp_statement_end", rename "Foreign.Statement_end");
    ("Wp_text", rename "Foreign.Wrapper_text");
    ("Wp_element", rename "Foreign.Wrapper_element");
    ("Foreign_constant", rename "Foreign.Constant");
    ("Foreign_call", rename "Foreign.Call");
    ("Foreign_block", rename "Foreign.Block_value");
    ("Foreign_statements", rename "Foreign.Statements");
    ("Declared", Not_syntax "a site Minicpp.spell_arrows spells a function type at");
    ("Through_tvar", Not_syntax "a site Minicpp.spell_arrows spells a function type at");
    ("Declared_at", Not_syntax "a site Minicpp.spell_arrows spells a function type at");
    ("Dtemplate", rename "Decl.Template");
    ("Dnspace", rename "Decl.Namespace");
    ("Dfun", rename "Decl.Function");
    ("Dstruct", rename "Decl.Struct");
    ("Dasgn", rename "Decl.Variable");
    ("Dconcept", rename "Decl.Concept");
    ("Dstatic_assert", rename "Decl.Static_assert");
    ("Dusing", rename "Decl.Type_alias");
    ("Dstruct_fwd", rename "Decl.Struct_forward_declaration");
    ("Dfields", rename "Decl.Merged_struct_members");
    ("Dmember_def", rename "Decl.Member_definition");
    ("Denum", rename "Decl.Enum");
    ("Ddef", rename "Function.Definition");
    ("Ddecl", rename "Function.Declaration") ]

(* Source text with comments and string literals blanked out, line breaks
   kept: nested comments, and string literals inside a comment, as OCaml
   lexes them. *)
let strip_comments s =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let keep_newline c = if c = '\n' then Buffer.add_char b '\n' in
  let rec code i =
    if i >= n then ()
    else if i + 1 < n && s.[i] = '(' && s.[i + 1] = '*' then comment 1 (i + 2)
    else if s.[i] = '"' then string (i + 1) code
    else begin
      Buffer.add_char b s.[i];
      code (i + 1)
    end
  and comment depth i =
    if i >= n then ()
    else if i + 1 < n && s.[i] = '(' && s.[i + 1] = '*' then comment (depth + 1) (i + 2)
    else if i + 1 < n && s.[i] = '*' && s.[i + 1] = ')' then
      if depth = 1 then code (i + 2) else comment (depth - 1) (i + 2)
    else if s.[i] = '"' then string (i + 1) (comment depth)
    else begin
      keep_newline s.[i];
      comment depth (i + 1)
    end
  and string i k =
    if i >= n then ()
    else if s.[i] = '\\' then string (i + 2) k
    else if s.[i] = '"' then k (i + 1)
    else begin
      keep_newline s.[i];
      string (i + 1) k
    end
  in
  code 0;
  Buffer.contents b

let read file = In_channel.with_open_bin file In_channel.input_all

let is_ident_char = function 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true | _ -> false

let is_blank = function ' ' | '\n' | '\t' -> true | _ -> false

(* The identifier at [i] in [s], blanks skipped, if it is capitalised, and
   where it ends. *)
let capitalised_at s i =
  let n = String.length s in
  let rec skip i = if i < n && is_blank s.[i] then skip (i + 1) else i in
  let i = skip i in
  if i < n && s.[i] >= 'A' && s.[i] <= 'Z' then begin
    let j = ref i in
    while !j < n && is_ident_char s.[!j] do
      incr j
    done;
    Some (String.sub s i (!j - i), !j)
  end
  else None

(* What follows position [j] of [s], blanks skipped. *)
let rest_at s j =
  let n = String.length s in
  let rec skip i = if i < n && is_blank s.[i] then skip (i + 1) else i in
  let i = skip j in
  String.sub s i (n - i)

(* The constructors a comment-free source declares, each with the text its
   declaration spans (up to the next bar or [end]): a capitalised identifier
   after a single [|], or after the [=] of a one-line [type]/[and] head when
   what follows it is [of], a bar, a colon, or the end of the line. *)
let constructors s =
  let n = String.length s in
  let span j =
    let rec stop k =
      if k >= n || s.[k] = '|' then k
      else if k + 3 <= n && String.sub s k 3 = "end" && (k = 0 || not (is_ident_char s.[k - 1])) then k
      else stop (k + 1)
    in
    String.sub s j (stop j - j)
  in
  let found = ref [] in
  for i = 0 to n - 1 do
    if s.[i] = '|' && not ((i + 1 < n && s.[i + 1] = '|') || (i > 0 && s.[i - 1] = '|')) then
      match capitalised_at s (i + 1) with Some (c, j) -> found := (c, span j) :: !found | None -> ()
  done;
  let offset = ref 0 in
  List.iter
    (fun line ->
      let trimmed = String.trim line in
      ( if (String.starts_with ~prefix:"type " trimmed || String.starts_with ~prefix:"and " trimmed)
           && String.contains line '='
      then
        let eq = String.index line '=' in
        match capitalised_at line (eq + 1) with
        | Some (c, j) ->
          let rest = String.trim (String.sub line j (String.length line - j)) in
          if rest = "" || String.starts_with ~prefix:"of " rest || String.starts_with ~prefix:"|" rest
             || String.starts_with ~prefix:":" rest
          then found := (c, span (!offset + j)) :: !found
        | None -> () );
      offset := !offset + String.length line + 1 )
    (String.split_on_char '\n' s);
  List.rev !found

(* The grammar's recursive modules, each with the constructors it declares
   and whether each is declared at [lowered] only. *)
let grammar_modules file =
  let lines = String.split_on_char '\n' (strip_comments (read file)) in
  let header line =
    let rest =
      if String.starts_with ~prefix:"module rec " line then Some (String.sub line 11 (String.length line - 11))
      else if String.starts_with ~prefix:"and " line then Some (String.sub line 4 (String.length line - 4))
      else None
    in
    match rest with
    | Some r -> (
      match capitalised_at r 0 with
      | Some (m, j) when String.starts_with ~prefix:": sig" (rest_at r j) -> Some m
      | _ -> None )
    | None -> None
  in
  let modules = ref [] and current = ref None and body = Buffer.create 1024 in
  let close () =
    Option.iter
      (fun m ->
        let ctors = constructors (Buffer.contents body) in
        let lowered (_, text) =
          let t = String.concat " " (String.split_on_char '\n' text) in
          (* Its result type is at [lowered]: [C : lowered t], or
             [C : a -> lowered t]. *)
          let rec has i =
            i + 10 <= String.length t
            && (String.sub t i 10 = "-> lowered" || String.sub t i 9 = ": lowered" || has (i + 1))
          in
          has 0
        in
        modules := (m, List.map (fun (c, text) -> (c, lowered (c, text))) ctors) :: !modules)
      !current;
    Buffer.clear body
  in
  List.iter
    (fun line ->
      match header line with
      | Some m ->
        close ();
        current := Some m
      | None ->
        Buffer.add_string body line;
        Buffer.add_char body '\n')
    lines;
  close ();
  !modules

(* The families: each file of src/cpp_ir other than the grammar that
   re-exports a grammar module, by public path.  [include Grammar.X] in
   [f.ml] makes [F] the module [X]; [module M = Grammar.Y] makes [F.M] the
   module [Y]. *)
let families dir =
  Sys.readdir dir |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".ml" && f <> "grammar.ml")
  |> List.concat_map (fun f ->
         let family = String.capitalize_ascii (Filename.chop_suffix f ".ml") in
         String.split_on_char '\n' (strip_comments (read (Filename.concat dir f)))
         |> List.filter_map (fun line ->
                let line = String.trim line in
                if String.starts_with ~prefix:"include Grammar." line then
                  Some (family, String.sub line 16 (String.length line - 16))
                else if String.starts_with ~prefix:"module " line then
                  match String.split_on_char '=' line with
                  | [lhs; rhs] ->
                    let rhs = String.trim rhs and lhs = String.trim (String.sub lhs 7 (String.length lhs - 7)) in
                    if String.starts_with ~prefix:"Grammar." rhs then
                      Some (family ^ "." ^ lhs, String.sub rhs 8 (String.length rhs - 8))
                    else None
                  | _ -> None
                else None))

let () =
  let minicpp = constructors (strip_comments (read "../src/minicpp.mli")) |> List.map fst in
  let grammar = grammar_modules "../src/cpp_ir/grammar.ml" in
  let families = families "../src/cpp_ir" in
  let obligations =
    constructors (strip_comments (read "../src/cpp_ir/representation_obligation.mli")) |> List.map fst
  in
  let errors = ref [] in
  let error fmt = Printf.ksprintf (fun s -> errors := s :: !errors) fmt in
  let classified = List.map fst manifest in
  List.iter (fun c -> if not (List.mem c classified) then error "%s: declared by minicpp.mli, not in the manifest" c) minicpp;
  List.iter (fun c -> if not (List.mem c minicpp) then error "%s: in the manifest, not declared by minicpp.mli" c) classified;
  List.iter
    (fun c -> if List.length (List.filter (( = ) c) classified) > 1 then error "%s: classified more than once" c)
    (List.sort_uniq compare classified);
  let target_lowered c target =
    match List.rev (String.split_on_char '.' target) with
    | ctor :: (_ :: _ as rev_path) -> (
      let path = String.concat "." (List.rev rev_path) in
      match List.assoc_opt path families with
      | None -> error "%s: %s names %s, which no file of src/cpp_ir re-exports" c target path; None
      | Some m -> (
        match List.assoc_opt m grammar with
        | None -> error "%s: %s names Grammar.%s, which the grammar does not declare" c target m; None
        | Some ctors -> (
          match List.assoc_opt ctor ctors with
          | None -> error "%s: Grammar.%s declares no constructor %s" c m ctor; None
          | Some lowered -> Some lowered ) ) )
    | _ ->
      error "%s: %s is not a family path" c target;
      None
  in
  List.iter
    (fun (c, k) ->
      match k with
      | Rename t -> (
        match target_lowered c t with
        | Some true -> error "%s: %s is declared at lowered only, but the manifest renames it" c t
        | _ -> () )
      | Lowered (t, o) -> (
        if not (List.mem o obligations) then error "%s: %s is not a representation obligation" c o;
        match target_lowered c t with
        | Some false -> error "%s: %s is not declared at lowered only" c t
        | _ -> () )
      | Dead _ | Not_syntax _ -> ())
    manifest;
  let count p = List.length (List.filter (fun (_, k) -> p k) manifest) in
  Printf.printf "%d constructors: %d renamed, %d lowered only, %d dead, %d not syntax\n" (List.length minicpp)
    (count (function Rename _ -> true | _ -> false))
    (count (function Lowered _ -> true | _ -> false))
    (count (function Dead _ -> true | _ -> false))
    (count (function Not_syntax _ -> true | _ -> false));
  match List.rev !errors with
  | [] -> ()
  | es ->
    List.iter prerr_endline es;
    exit 1
