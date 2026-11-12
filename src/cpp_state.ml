(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Mutable state and utility functions for C++ printing.

    This module holds the global mutable state (hashtables, refs) shared by
    the modules that print the finished CppIR program, the position type
    ({!render_ctx}) they hand each other, and small utility functions that
    depend on that state. Centralising state here avoids circular
    dependencies between the other cpp_* modules. *)

open Pp
open Names
open Table
open Common

(** {2 Owned cells}

    Every mutable cell this module owns is created by one of the constructors
    below, which enrol it in {!reset_cpp_state} and in {!Table.census} at the
    point it is defined, so no cell can exist that the reset or the census
    misses. *)

let on_reset f = State.on_reset State.Extraction f

(** A hash table owned by this module, emptied between extractions.

    @param census
      report the table's size to {!Table.census} under [name].  Pass [false] for
      a cell that emission legitimately fills, which the census's late-decision
      check reads as a decision taken too late. *)
let owned_table ?(census = true) name =
  let t = Hashtbl.create 16 in
  on_reset (fun () -> Hashtbl.clear t);
  if census then Table.register_census name (fun () -> Hashtbl.length t);
  t

(** A list-valued ref owned by this module, emptied between extractions.  See
    {!owned_table} for [census]. *)
let owned_list ?(census = true) name =
  let r = ref [] in
  on_reset (fun () -> r := []);
  if census then Table.register_census name (fun () -> List.length !r);
  r

(** A ref owned by this module, restored to [init] between extractions.  It
    holds one thing rather than a set of them, so there is nothing to census. *)
let owned_ref init =
  let r = ref init in
  on_reset (fun () -> r := init);
  r

(** The method registry, created once per extraction pass by scanning the
    full ml_structure.  Queries go through {!get_method_registry}. *)
let method_registry : Method_registry.t option ref = owned_ref None

(** In separate extraction, a pre-built method registry from the full
    structure is used so that cross-module method calls are recognized. *)
let global_method_registry : Method_registry.t option ref = owned_ref None

let set_global_method_registry reg = global_method_registry := Some reg
let clear_global_method_registry () = global_method_registry := None

(** Get the method registry, raising an anomaly if not initialized. *)
let get_method_registry () =
  match !method_registry with
  | Some r -> r
  | None -> CErrors.anomaly (Pp.str "method_registry not initialized.")

(** Pre-computed name resolution cache, populated once per extraction pass.
    Queries go through {!get_name_cache}. *)
let name_cache : Name_resolution.t option ref = owned_ref None

(** Get the name cache, raising an anomaly if not initialized. *)
let get_name_cache () =
  match !name_cache with
  | Some c -> c
  | None -> CErrors.anomaly (Pp.str "name_cache not initialized.")

(** {2 Some utility functions.} *)

(** Pretty-print a type variable as a string. *)
let pp_tvar id = str (Id.to_string id)

(** Pretty-print type parameters as a boxed tuple with optional trailing space.
*)
let pp_parameters l = pp_boxed_tuple pp_tvar l ++ space_if (l <> [])

(** Pretty-print string parameters as a boxed tuple with optional trailing
    space. *)
let pp_string_parameters l = pp_boxed_tuple str l ++ space_if (l <> [])

(** Helper to get custom type mapping with ids, returning option *)
let find_type_custom_opt r =
  if is_custom r then
    (* Safe to call find_type_custom since is_custom returned true *)
    Some (find_type_custom r)
  else
    None

(** {2 C++ renaming issues.} *)

(** Set of C++ keywords and reserved identifiers that must be avoided. *)
let keywords =
  List.fold_right
    (fun s -> Id.Set.add (Id.of_string s))
    [
      (* C++ keywords *)
      "alignas";
      "alignof";
      "and";
      "and_eq";
      "asm";
      "auto";
      "bitand";
      "bitor";
      "bool";
      "break";
      "case";
      "catch";
      "char";
      "char8_t";
      "char16_t";
      "char32_t";
      "class";
      "compl";
      "concept";
      "const";
      "consteval";
      "constexpr";
      "constinit";
      "const_cast";
      "continue";
      "co_await";
      "co_return";
      "co_yield";
      "decltype";
      "default";
      "delete";
      "do";
      "double";
      "dynamic_cast";
      "else";
      "enum";
      "explicit";
      "export";
      "extern";
      "false";
      "float";
      "for";
      "friend";
      "goto";
      "if";
      "inline";
      "int";
      "long";
      "mutable";
      "namespace";
      "new";
      "noexcept";
      "not";
      "not_eq";
      "nullptr";
      "operator";
      "or";
      "or_eq";
      "private";
      "protected";
      "public";
      "register";
      "reinterpret_cast";
      "requires";
      "return";
      "short";
      "signed";
      "sizeof";
      "static";
      "static_assert";
      "static_cast";
      "struct";
      "switch";
      "template";
      "this";
      "thread_local";
      "throw";
      "true";
      "try";
      "typedef";
      "typeid";
      "typename";
      "union";
      "unsigned";
      "using";
      "virtual";
      "void";
      "volatile";
      "wchar_t";
      "while";
      "xor";
      "xor_eq";
      (* Reserved identifiers *)
      "_";
      "__";
      (* Unqualified library names that Crane's type mappings and runtime
         headers put at global scope.  A Rocq definition or inductive with one
         of these names would shadow the type it is spelled with — e.g. a
         [Definition uint64_t] inside a struct hides the [uint64_t] used for
         its own signature, and an [Inductive List] hides the runtime's
         [List<T>]. *)
      "int8_t";
      "int16_t";
      "int32_t";
      "int64_t";
      "uint8_t";
      "uint16_t";
      "uint32_t";
      "uint64_t";
      "intptr_t";
      "uintptr_t";
      "ptrdiff_t";
      "size_t";
      "List";
      (* Macros the C standard headers define.  The preprocessor runs before
         any scope, so a declaration spelled like one is rewritten before the
         compiler sees it -- [static Request alloca(Nat, Nat, bool)] against
         <alloca.h> is "too many arguments provided to function-like macro".
         An enum constructor is upper-cased, so [Inductive c := NaN | NZero]
         meets <cmath>'s [NAN] and <limits.h>'s [NZERO].  Only the spelling
         the header uses is reserved; the case-folded forms are separate
         names to the preprocessor. *)
      "alloca";
      "va_start";
      "va_end";
      "va_copy";
      "va_arg";
      "TRUE";
      "FALSE";
      "NULL";
      "EOF";
      "DOMAIN";
      "OVERFLOW";
      "UNDERFLOW";
      "HUGE_VAL";
      "ERANGE";
      "STDIN";
      "STDOUT";
      "STDERR";
      "NAN";
      "INFINITY";
      "HUGE_VALF";
      "HUGE_VALL";
      "FP_NAN";
      "FP_INFINITE";
      "FP_ZERO";
      "FP_SUBNORMAL";
      "FP_NORMAL";
      "MATH_ERRNO";
      "MATH_ERREXCEPT";
      "math_errhandling";
      "errno";
      "EDOM";
      "EILSEQ";
      "EXIT_SUCCESS";
      "EXIT_FAILURE";
      "RAND_MAX";
      "MB_CUR_MAX";
      "BUFSIZ";
      "FILENAME_MAX";
      "FOPEN_MAX";
      "SEEK_SET";
      "SEEK_CUR";
      "SEEK_END";
      "TMP_MAX";
      "stdin";
      "stdout";
      "stderr";
      "assert";
      "offsetof";
      "CHAR_BIT";
      "INT_MAX";
      "INT_MIN";
      "UINT_MAX";
      "LONG_MAX";
      "LONG_MIN";
      "ULONG_MAX";
      "LLONG_MAX";
      "LLONG_MIN";
      "ULLONG_MAX";
      "CHAR_MAX";
      "CHAR_MIN";
      "SCHAR_MAX";
      "SCHAR_MIN";
      "UCHAR_MAX";
      "SHRT_MAX";
      "SHRT_MIN";
      "USHRT_MAX";
      "MB_LEN_MAX";
      "NZERO";
      "PATH_MAX";
      "NAME_MAX";
      "ARG_MAX";
      "CHILD_MAX";
      "OPEN_MAX";
      "LINE_MAX";
      "PIPE_BUF";
      "NGROUPS_MAX";
      "SIZE_MAX";
      "INT64_MAX";
      "INT64_MIN";
      "UINT64_MAX";
      "INT64_C";
      "UINT64_C";
    ]
    (* The namespaces and global names the runtime is spelled with: a
       [crane] or [std] declared in a struct hides [crane::rc] or
       [std::shared_ptr] from every member after it. *)
    (List.fold_right
       (fun s -> Id.Set.add (Id.of_string s))
       Table.reserved_global_cpp_names Id.Set.empty)

(** Names the C and POSIX libraries declare at global scope.

    These are functions, so a Crane declaration of the same name is usually
    just another overload beside them -- harmless, and far too common a
    spelling to rewrite everywhere.  What the compiler refuses is a *different*
    kind of entity under the name: [Definition select := nat] at the root of an
    extraction becomes [using select = uint64_t;] beside the [::select] that
    <sys/select.h> declares, which is "redefinition of 'select' as a different
    kind of symbol".

    So these are reserved only where a declaration reaches global scope, and
    left alone inside a namespace or struct, where no C library name can reach
    them.  See {!Common.is_reserved_at_global_scope}. *)
let c_library_globals =
  List.fold_right
    (fun s -> Id.Set.add (Id.of_string s))
    [
      (* <cstdlib>, <cstring>, <cstdio>, <ctime>, <csignal> *)
      "abort"; "abs"; "atexit"; "atof"; "atoi"; "atol"; "bsearch"; "calloc";
      "div"; "exit"; "free"; "getenv"; "labs"; "ldiv"; "malloc"; "qsort";
      "rand"; "realloc"; "srand"; "system";
      "memchr"; "memcmp"; "memcpy"; "memmove"; "memset"; "strcat"; "strchr";
      "strcmp"; "strcoll"; "strcpy"; "strcspn"; "strerror"; "strlen";
      "strncat"; "strncmp"; "strncpy"; "strpbrk"; "strrchr"; "strspn";
      "strstr"; "strtok"; "strxfrm";
      "fclose"; "feof"; "ferror"; "fflush"; "fgetc"; "fgets"; "fopen";
      "fprintf"; "fputc"; "fputs"; "fread"; "freopen"; "fscanf"; "fseek";
      "ftell"; "fwrite"; "getc"; "getchar"; "perror"; "printf"; "putc";
      "putchar"; "puts"; "remove"; "rename"; "rewind"; "scanf"; "setbuf";
      "sprintf"; "sscanf"; "tmpfile"; "tmpnam"; "ungetc";
      "asctime"; "clock"; "ctime"; "difftime"; "gmtime"; "localtime";
      "mktime"; "strftime"; "time"; "timezone";
      "raise"; "signal"; "longjmp"; "setjmp";
      "isalnum"; "isalpha"; "iscntrl"; "isdigit"; "isgraph"; "islower";
      "isprint"; "ispunct"; "isspace"; "isupper"; "isxdigit"; "tolower";
      "toupper";
      (* <cmath> *)
      "acos"; "asin"; "atan"; "atan2"; "ceil"; "cos"; "cosh"; "exp"; "fabs";
      "floor"; "fmod"; "frexp"; "ldexp"; "log"; "log10"; "modf"; "pow"; "sin";
      "sinh"; "sqrt"; "tan"; "tanh"; "gamma"; "j0"; "j1"; "jn"; "y0"; "y1";
      "yn";
      (* POSIX headers the C++ standard headers pull in *)
      "accept"; "access"; "alarm"; "bind"; "chdir"; "chmod"; "chown"; "close";
      "connect"; "dup"; "dup2"; "execl"; "execv"; "fork"; "fstat"; "fsync";
      "ftruncate"; "getcwd"; "getline"; "getpid"; "getuid"; "index"; "kill";
      "link"; "listen"; "lseek"; "mkdir"; "open"; "pause"; "pclose"; "pipe";
      "popen"; "random"; "read"; "readlink"; "recv"; "rindex"; "rmdir";
      "select"; "send"; "setlocale"; "sleep"; "socket"; "srandom"; "stat";
      "symlink"; "sync"; "times"; "truncate"; "unlink"; "usleep"; "wait";
      "waitpid"; "write";
    ]
    Id.Set.empty

(** Note: do not shorten [str "foo" ++ fnl ()] into [str "foo\n"], the '\n'
    character interacts badly with the Format boxing mechanism *)

(** Set of module paths that produce output files in separate extraction.
    When non-empty, pp_open skips modules not in this set. *)
let valid_output_modules : (ModPath.t, unit) Hashtbl.t =
  owned_table ~census:false "valid_output_modules"

(** Set the modules that are allowed to produce output in this extraction run.
    Only modules in [mps] will emit #include directives via [pp_open].
    @param mps list of module paths that should produce output files *)
let set_valid_output_modules mps =
  Hashtbl.clear valid_output_modules;
  List.iter (fun mp -> Hashtbl.replace valid_output_modules mp ()) mps

let clear_valid_output_modules () = Hashtbl.clear valid_output_modules

(** The wrapper struct names that stay unmerged across the passes of a
    separate extraction ({!mark_global_unmerged}). *)
let global_unmerged_wrappers : (string, unit) Hashtbl.t =
  owned_table "global_unmerged_wrappers"

(** Record that wrapper [name] must remain unmerged across extraction passes.
    Used in separate extraction so that inter-module references use the
    unmerged (qualified) form even for modules processed in a prior pass.
    @param name the C++ wrapper struct name to mark as unmerged *)
let mark_global_unmerged name =
  Hashtbl.replace global_unmerged_wrappers name ()

(** Check whether wrapper [name] was recorded as globally unmerged.
    @param name the C++ wrapper struct name to query
    @return [true] if [name] must use the unmerged (qualified) name form *)
let is_global_unmerged name =
  Hashtbl.mem global_unmerged_wrappers name

let clear_global_unmerged () =
  Hashtbl.clear global_unmerged_wrappers

(** Pretty-print an open directive for a module. *)
let pp_open mp =
  if Hashtbl.length valid_output_modules > 0
     && not (Hashtbl.mem valid_output_modules mp) then
    mt ()
  else
    str ("#include \"" ^ file_of_modfile mp ^ ".h\"") ++ fnl ()

(** The text [s] as C++ line comments, one per line of [s]: a line comment
    ends at its newline, so no text it holds -- a star-slash included -- can
    end it early. *)
let pp_comment s =
  prlist_with_sep fnl (fun l -> str ("// " ^ l)) (String.split_on_char '\n' s)

(** Pretty-print an optional header comment. *)
let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ fnl2 ()

(** Add a newline after pp if it's non-empty. *)
let then_nl pp = if Pp.ismt pp then mt () else pp ++ fnl ()

(** Generate preamble for implementation files.
    @param comment optional header comment to emit at the top of the file
    @param used_modules list of module paths whose headers must be #included
    @return pretty-printed preamble consisting of the comment and #include lines *)
let preamble _ comment used_modules _usf =
  pp_header_comment comment ++ then_nl (prlist pp_open used_modules)

(** Generate preamble for signature/header files.
    @param comment optional header comment to emit at the top of the file
    @param used_modules list of module paths whose headers must be #included
    @return pretty-printed preamble consisting of the comment and #include lines *)
let sig_preamble _ comment used_modules _usf =
  pp_header_comment comment ++ then_nl (prlist pp_open used_modules)

(** {2 Render context} *)

(** Where a synthesised template is declared: inside the struct of a
    module, as its members are written, or at namespace scope, beneath the
    unit's files, innermost last -- the files as the module whose element
    first spelled it sees them. *)
type declared_in = In_struct_of of ModPath.t | At_namespace_scope of ModPath.t list

(** A parameter of a holder ({!ctor_alias}), as its body writes it: a
    captured variable written applied to the alias's own argument, a type
    constructor ([template <typename> class F0]); one written bare, or a
    class instance the body reads a type out of, a type ([typename P1]). *)
type holder_parameter = Constructor_parameter of Names.Id.t | Type_parameter of Names.Id.t

(** What a holder is applied to where it is written, the argument for each
    of its parameters in order: a type variable of the enclosing declaration
    its body captures, by index (and the name it is written by, where it
    carries one), or a class instance its body reads a type out of. *)
type holder_argument = Captured_variable of int * Names.Id.t option | Captured_instance of Names.Id.t

(** A template synthesised for a type constructor with no template name of
    its own, where it is spelled as a template template argument
    ({!Cpp_leaf_plan.ctor_alias_at}). *)
type ctor_alias = {
  ca_base : string;  (** What its name is made from. *)
  ca_holder : holder_parameter list option;
  ca_declared : declared_in;  (** Where it is declared ({!Cpp_leaf_plan.ctor_alias_declared}). *)
  ca_body : string;
      (** The type it abbreviates, as written where it is declared, with the
          sentinel where the template's own parameter goes. *)
  ca_type : Cpp_ir.Resolved.Type.t;  (** That type. *)
  ca_vars : Id.t list;  (** The names of the variables it names by index. *)
  ca_uses : tyctor_use list;  (** How its body writes the type constructors in it. *)
}

(** How a type constructor written as a template template argument is
    written, decided where it is planned: the constructor, the names of the
    type variables it names by index, and the template synthesised for it
    with the arguments a holder is applied to, if it has no template name
    of its own ({!Cpp_leaf_plan.ctor_alias_at}). *)
and tyctor_use = {
  tu_constructor : Cpp_ir.Resolved.Type.t;
  tu_vars : Id.t list;
  tu_alias : (ctor_alias * holder_argument list) option;
}

(** What the names written at a position are read off: nothing, where
    naming anything is an anomaly; the program, where the resolver names
    each key where it stands, through the namers it hands the position
    ({!Cpp_names.live_name}); or the names of the declaration being written,
    resolved before it is written. *)
type naming = No_names | Naming_live of live_namers | Names_resolved of Cpp_resolution.table

(* How the resolver names, at a position, a key, a global, and the inline
   custom text of a global, if it has one, writes a global type's head, and
   answers any key: what the naming functions shared with the printer call
   where the resolver uses them. *)
and live_namers = {
  live_key : render_ctx -> Cpp_resolution.key -> Cpp_name.t;
  live_global : render_ctx -> Common.kind -> GlobRef.t -> Cpp_name.t;
  live_inline : GlobRef.t -> string option;
  live_head : render_ctx -> Cpp_resolution.head_form -> GlobRef.t -> Cpp_resolution.head;
  live_value : render_ctx -> Cpp_resolution.key -> Cpp_resolution.value;
}

(** Where the type printer reads how a type constructor is written: nowhere,
    where writing one is an anomaly; off planning, which decides it where it
    is spelled and notes it; or off the plan of the leaf being printed. *)
and tyctor_plan = Unplanned | Deciding of tyctor_decision | Planned of tyctor_use list

(* How planning decides, at a position, how a type constructor naming the
   given variables is written, and the uses it has decided, in the order
   first spelled. *)
and tyctor_decision = {
  decide : render_ctx -> Id.t list -> Cpp_ir.Resolved.Type.t -> (ctor_alias * holder_argument list) option;
  noted : tyctor_use list ref;
}

(** The out-of-line definition being written: the scope it is a member
    of, and the promoted type variables whose alias its file declares at
    file scope. *)
and out_of_line = {
  ol_scope : Scope_plan.scope;
  ol_file_scope_aliases : Id.Set.t;
}

(** Where in the output something is written or planned: a value, handed
    to whatever writes there and derived as each scope is entered.  No
    position is installed anywhere for a reader to find. *)
and render_ctx = {
  (* The file being written. *)
  rc_file : Common.file;
  (* Inside a struct body? Affects qualification of nested type references. *)
  rc_in_struct : bool;
  (* Type_class concepts already emitted for the current module? *)
  rc_concepts_hoisted : bool;
  (* The out-of-line definition being printed, if one is: the struct it is
     a member of, which a name written outside that struct's body is
     qualified by, and the type names its file declares at file scope.  Set
     by the definition, from the plans. *)
  rc_scope : out_of_line option;
  (* Inside a template struct (functor)? Affects typename keyword insertion. *)
  rc_in_template : bool;
  (* The module whose element is being written, if one is: said by whatever
     writes or plans it, from the module it is an element of. *)
  rc_module : Names.ModPath.t option;
  (* The scopes printing the declaration being written has entered inside
     the one it is written in, innermost first ({!Cpp_names.enter}). *)
  rc_frame : Cpp_resolution.frame;
  (* What the names written here are read off. *)
  rc_names : naming;
  (* The scopes whose names are visible where the declaration being written
     is written, innermost first: its planned visibility; none where nothing
     planned it, where nothing may be named.  The layers of the scopes
     entered inside it are added where the resolver reads it
     ({!Cpp_names.visibility_at}). *)
  rc_visibility : Common.visibility option;
  (* Where the synthesised templates spelled from here are collected, if
     anything collects them. *)
  rc_aliases : ctor_alias list ref option;
  (* How the type constructors written from here are written. *)
  rc_tyctors : tyctor_plan;
}

(** The context at the start of the file [file]: file scope, outside every
    struct. *)
let file_start rc_file =
  {
    rc_file;
    rc_in_struct = false;
    rc_concepts_hoisted = false;
    rc_scope = None;
    rc_in_template = false;
    rc_module = None;
    rc_frame = [];
    rc_names = No_names;
    rc_visibility = None;
    rc_aliases = None;
    rc_tyctors = Unplanned;
  }

(** What a file declares at file scope: the types, by the entity each
    declaration declares, and the promoted type variables among them, by
    the name of their alias. *)
type file_scope = {
  fs_types : GlobRef.Set.t;
  fs_aliases : Id.Set.t;
}

(* What the header declares at file scope: the types (an erased type-class
   field's [using], a wrapper, a struct), and among them the promoted type
   variables' aliases.  A definition written out of line qualifies the plain
   names in its signature with its struct's, which is right for a member and
   wrong for one of these aliases. *)
let header_file_scope : file_scope option ref = State.cell State.Unit None

let file_scope_types_of file =
  match (file, !header_file_scope) with
  | Common.Intf, Some fs -> fs.fs_types
  | (Common.Intf | Common.Impl), _ -> GlobRef.Set.empty

let file_scope_aliases_of file =
  match (file, !header_file_scope) with
  | Common.Intf, Some fs -> fs.fs_aliases
  | (Common.Intf | Common.Impl), _ -> Id.Set.empty

(** The modules whose module types are file-scope concepts of a functor
    ({!Module_plan.concept_scope}): a functor's body, an application of the
    functor, an alias of the application. *)
let functor_concept_scopes : (Names.ModPath.t * Module_plan.concept_scope) list ref =
  owned_list "functor_concept_scopes"


(** A concept a frame is holding back until after the struct it was written
    in, identified by whatever declares it. *)
type held_concept =
  | HCmodtype of Names.ModPath.t  (** a module type's concept *)
  | HCclass of Names.GlobRef.t  (** a type class's concept *)

(** Equality on {!held_concept}. *)
let held_concept_equal a b =
  match (a, b) with
  | HCmodtype x, HCmodtype y -> Names.ModPath.equal x y
  | HCclass x, HCclass y -> globref_equal x y
  | _ -> false

(** Whether a concept is one the current frame is holding back. *)
let is_held_back_in held_back c =
  List.exists (held_concept_equal c) held_back

(** Where the header declares one of a module's concepts: ahead of its
    struct, after it (when it names a member), or at file scope (when the
    module is nested in a struct, where no concept can be declared). *)
type concept_placement = Ahead_of_struct | After_struct | At_file_scope

(** The concepts of a module, planned ahead of the files: where each is
    declared, and which its struct's body treats as not declared yet. *)
type concept_plan = {
  placements : (held_concept * concept_placement) list;
  held_back : held_concept list;
}

(* The concept plan of each module of the unit, by module path. *)
let concept_plans : concept_plan Names.MPmap.t ref = State.cell State.Unit Names.MPmap.empty

let plan_module_concepts mp plan = concept_plans := Names.MPmap.add mp plan !concept_plans

let concept_plan mp =
  match Names.MPmap.find_opt mp !concept_plans with
  | Some plan -> plan
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: the module " ++ str (Names.ModPath.to_string mp) ++ str " has no planned concepts.")

let planned_held_back ~file mp =
  match (file : Common.file) with
  | Intf -> (
    match Scope_plan.frames mp with
    | Some frames -> List.concat_map (fun m -> (concept_plan m).held_back) frames
    | None ->
      CErrors.anomaly
        Pp.(str "Crane: the body of the module " ++ str (Names.ModPath.to_string mp) ++ str " has no planned frames.") )
  | Impl -> []

let concept_held_back ctx c =
  ctx.rc_in_struct
  && match ctx.rc_module with Some mp -> is_held_back_in (planned_held_back ~file:ctx.rc_file mp) c | None -> false

let class_concept_held_back ctx r = concept_held_back ctx (HCclass r)

let element_position mp c =
  if c.rc_frame <> [] then
    CErrors.anomaly (Pp.str "Crane: a module's element is written inside a scope a declaration entered.");
  {c with rc_module = Some mp; rc_visibility = Scope_plan.visibility mp}

(** The globals the unit's function bodies name, planned from the unit's
    installed declarations before either file is rendered ({!Cpp.plan_function_reads}):
    [None] until planned.  Compared by the definition a name reaches, so a
    read through a module alias counts. *)
let function_reads : Ref.Can.Set.t option ref = owned_ref None

(* What the declarations of every unit of a separate extraction name, from
   the whole program before any unit is generated: another unit's function
   is not generated when this one is planned. *)
let program_reads : Ref.Can.Set.t ref = owned_ref Ref.Can.Set.empty

let note_program_reads s = program_reads := s
let plan_function_reads s = function_reads := Some (Ref.Can.Set.union s !program_reads)

let read_by_a_function r =
  match !function_reads with
  | Some s -> Ref.Can.Set.mem r s
  | None -> false

(** Track definitions rendered as function accessors (Meyers singletons) instead
    of static inline variables, due to template static init ordering. Stores
    both (modpath, label) pairs for direct matching and canonical KerNames for
    a constant reached through a module alias. *)
let template_static_accessors : (ModPath.t * Label.t) list ref =
  owned_list "template_static_accessors"
let template_static_accessor_kns : (KerName.t, unit) Hashtbl.t =
  owned_table "template_static_accessor_kns"

(** Record a definition as a template static accessor (Meyers singleton).
    Definitions rendered this way are emitted as inline functions rather than
    static inline variables to avoid template static init ordering issues.

    Idempotent: the same definition is offered by the pre-scan over the ML
    structure and again when it is rendered, and the list is searched linearly
    on every call site's behalf.
    @param mp module path containing the definition
    @param lbl label (name) of the definition within the module *)
let register_template_static_accessor mp lbl =
  let known (mp', lbl') = ModPath.equal mp mp' && Label.equal lbl lbl' in
  if not (List.exists known !template_static_accessors) then
    template_static_accessors := (mp, lbl) :: !template_static_accessors

(** Whether the definition [lbl] of [mp] is recorded as an accessor. *)
let is_template_static_accessor mp lbl =
  List.exists (fun (mp', lbl') -> ModPath.equal mp mp' && Label.equal lbl lbl') !template_static_accessors

(** {!register_template_static_accessor} for a global reference, which also
    records the constant's kername for cross-functor matching. *)
let register_template_static_accessor_ref r =
  register_template_static_accessor (Table.modpath_of_r r) (Table.label_of_r r);
  match r with
  | GlobRef.ConstRef c ->
    Hashtbl.replace template_static_accessor_kns (Constant.canonical c) ()
  | _ -> ()


(** Track eponymous type info for method generation. When a module M contains an
    inductive type m (lowercase of M), functions taking an m as an argument
    become methods on m. *)
let eponymous_type_ref : GlobRef.t option ref = owned_ref None

(** Set during module rendering when the eponymous inductive should be promoted
    into the module struct. cpp_ind.ml checks this to render fields flat instead
    of a wrapping struct. *)
let eponymous_promote_ref : GlobRef.t option ref = owned_ref None


(** Collected method candidates: (function_ref, body, type, this_position) for
    current eponymous type. this_position is the index (0-based) of the first
    argument that matches the eponymous type. *)
let method_candidates :
    (GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int) list ref =
  owned_list "method_candidates"

(** Eponymous record: when a module M contains a record with the same name
    (e.g., module CHT with record CHT), we merge the record fields into the
    module struct to avoid C++ name conflicts. Stores: (record_ref, field_refs,
    ind_packet) *)
let eponymous_record :
    (GlobRef.t * Miniml.record_field list * Miniml.ml_ind_packet) option ref =
  owned_ref None

(** {2 Scoped render state}

    The position is a value handed to what writes there ({!render_ctx}).
    The state below is read in a dozen modules under its own names, so it
    stays in refs, and a scope brackets it instead. *)

(** A mutable cell a scope saves and restores, with its contents' type hidden
    so that cells of different types can be listed together. *)
type saver = Saver : 'a ref -> saver

(** [with_saved cells f] runs [f] and puts every cell in [cells] back the way
    it found it, however [f] leaves -- returning or raising.

    The point is to name the cells a scope owns in one place, and to restore
    them on an exception as well as on return. *)
let with_saved cells f =
  let restores =
    List.map
      (fun (Saver r) ->
        let v = !r in
        fun () -> r := v )
      cells
  in
  Fun.protect ~finally:(fun () -> List.iter (fun g -> g ()) restores) f

(** The state a module frame owns: what it says is true of the module now
    being rendered and of nothing outside it, so a nested render must not
    inherit it and the enclosing one must get it back.

    The position is not here: entering a module hands on another
    ({!Cpp_names.next}). *)
let module_frame_cells =
  [
    Saver eponymous_type_ref;
    Saver eponymous_record;
    Saver method_candidates;
  ]

(** [with_module_frame f] renders [f] as a module frame: it starts with no
    eponymous type, no eponymous record and no method candidates of its own,
    and leaves the enclosing frame's untouched. *)
let with_module_frame f =
  with_saved module_frame_cells (fun () ->
      eponymous_type_ref := None;
      eponymous_record := None;
      f () )

(** [setting cell v f] runs [f] with [cell] holding [v] and puts the enclosing
    contents back on the way out, however [f] leaves. *)
let setting cell v f =
  with_saved [Saver cell] (fun () ->
      cell := v;
      f () )

(** Resolved standard library names, computed once per extraction pass from
    [Table.std_lib ()] and the runtime flags ({!init_std_names}). *)
type std_names = {
  shared_ptr : string; (* "std::shared_ptr" or "bsl::shared_ptr" *)
  make_shared : string; (* "std::make_shared" or "bsl::make_shared" *)
  move : string; (* "std::move" or "bsl::move" *)
  forward : string; (* "std::forward" or "bsl::forward" *)
  logic_error : string; (* "std::logic_error" or "bsl::logic_error" *)
  ns : string; (* "std" or "bsl": general prefix *)
  string : string; (* "std::string" or "bsl::string" *)
  same_as : string; (* "std::same_as" or "same_as" *)
  declval : string; (* "std::declval" or "bsl::declval" *)
  convertible_to : string; (* "std::convertible_to" or "convertible_to" *)
  holds_alternative : string; (* "std::holds_alternative" or "bsl::holds_alternative" *)
  get_if : string; (* "std::get_if" or "bsl::get_if" *)
  get : string; (* "std::get" or "bsl::get" *)
  variant : string; (* "std::variant", "bsl::variant" or "crane::variant" *)
  variant_header : Table.header; (* the header [variant] is declared in *)
  enable_from_this : string; (* enable_shared_from_this base, or crane::enable_rc_from_this *)
}

let default_std_names =
  {
    shared_ptr = "std::shared_ptr";
    make_shared = "std::make_shared";
    move = "std::move";
    forward = "std::forward";
    logic_error = "std::logic_error";
    ns = "std";
    string = "std::string";
    same_as = "std::same_as";
    declval = "std::declval";
    convertible_to = "std::convertible_to";
    holds_alternative = "std::holds_alternative";
    get_if = "std::get_if";
    get = "std::get";
    variant = "std::variant";
    variant_header = Table.Standard "variant";
    enable_from_this = "std::enable_shared_from_this";
  }

(** The standard library names in effect, initialized by {!init_std_names}. *)
let std_names : std_names ref = ref default_std_names

let mk_std_names prefix =
  match prefix with
  | "bsl::" ->
    let p = prefix in
    { shared_ptr = p ^ "shared_ptr"; make_shared = p ^ "make_shared";
      move = p ^ "move"; forward = p ^ "forward";
      logic_error = p ^ "logic_error";
      ns = "bsl"; string = p ^ "string";
      same_as = "same_as"; declval = p ^ "declval";
      convertible_to = "convertible_to";
      holds_alternative = p ^ "holds_alternative";
      get_if = p ^ "get_if"; get = p ^ "get";
      variant = p ^ "variant"; variant_header = Table.Standard "variant";
      enable_from_this = p ^ "enable_shared_from_this" }
  | _ -> default_std_names

(** Initialize standard library names based on Table.std_lib() setting. *)
let init_std_names () =
  let base =
    if Table.std_lib () = "BDE" then mk_std_names "bsl::"
    else mk_std_names "std::"
  in
  (* [Crane NonAtomicRc]: swap the recursive-field smart pointer to the
     single-threaded, non-atomic [crane::rc] (with a matching from-this base).
     Namespace-neutral, so it overrides both the std and BDE flavors. *)
  (* [Crane FastVariant]: alternatives in [crane::variant], and the matching
     accessors. *)
  let base =
    if Table.fast_variant () then
      { base with
        variant = Crane_rt.variant;
        variant_header = Table.Runtime Crane_rt.variant_header;
        holds_alternative = "crane::holds_alternative";
        get_if = "crane::get_if";
        get = "crane::get" }
    else if Table.shared_variant () then
      (* [Crane SharedVariant] without FastVariant: inline types keep
         [std::variant], and every match reads through the [crane::]
         accessors, which take a shared variant and forward a [std::variant]
         to [std::]. *)
      { base with
        variant_header = Table.Runtime Crane_rt.variant_header;
        holds_alternative = "crane::holds_alternative";
        get_if = "crane::get_if";
        get = "crane::get" }
    else base
  in
  std_names :=
    (* [CRANE_COUNT_RC]: measurement build -- every shared pointer becomes the
       counting one.  [enable_from_this] stays as it is: [shared_from_this ()]
       hands back a [std::shared_ptr], which a [counting_ptr] adopts. *)
    if Table.count_rc () then
      { base with
        shared_ptr = Crane_rt.counting_ptr;
        make_shared = Crane_rt.make_counting }
    else if Table.non_atomic_rc () then
      { base with
        shared_ptr = Crane_rt.rc;
        make_shared = Crane_rt.make_rc;
        enable_from_this = Crane_rt.enable_rc_from_this }
    else base

(** Short accessor for current standard library names. *)
let sn () = !std_names

(** Whether a term is a typeclass instance: its final return type is a
    [Tglob] referencing a typeclass.
    @param _body the function body (unused; retained for API symmetry)
    @param ty the Miniml type of the term being tested
    @return [true] if the ultimate return type of [ty] is a registered typeclass *)
let is_typeclass_instance _body ty =
  let rec return_type = function
    | Miniml.Tarr (_, rest) -> return_type rest
    | t -> t
  in
  match return_type ty with
  | Miniml.Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false




(** Declarations a wrapper struct's module puts at namespace scope rather
    than in the struct.

    A module forced into a wrapper struct by a name collision does not take
    all of its declarations with it.  A type alias stays outside as
    [using T = ...;], because C++ puts it there; a type class instance is
    lifted out deliberately, because an instance is named from wherever its
    class is used and a concept's template argument is a type, not a member of
    whatever module happened to declare it.  Either way the wrapper struct
    does not declare the name, and {!wrapper_qualify} must not write
    [Wrapper::] in front of it.

    Asking where the name was {i emitted} is the only question that answers
    this; where it was {i declared} in Rocq says the opposite.  The answer is
    planned before any rendering begins ({!Module_plan.is_namespace_scope_ref}),
    which is what makes it safe to read from a [.cpp] body printed before the
    [.h] declares the name. *)

(** The wrapper structs that hold declarations of their module's and so
    cannot be merged with the eponymous inductive's struct, by struct name,
    with the module each wraps; planned ({!Cpp.plan_unmerged_wrappers}). *)
let unmerged_wrappers : (string, ModPath.t) Hashtbl.t =
  owned_table "unmerged_wrappers"

(** Whether the inductive [r] is written inside a wrapper that holds other
    declarations, and so is spelled [List::list] rather than [List].

    A property of [r]'s declaration, asked of the name its wrapper is named
    after -- its own short name -- and never of the way a use spells it: a use
    written through a qualifier names the same struct.  A type reached through
    a functor parameter is the parameter's member, in no wrapper; and a
    separately extracted file only plans its own wrappers, so a type of
    another file is not in one of them. *)
let in_unmerged_wrapper_named short r =
  let mp = modpath_of_r r in
  (not (Common.under_mp_bound mp))
  &&
  match Hashtbl.find_opt unmerged_wrappers (String.capitalize_ascii short) with
  | None -> false
  | Some wrapped ->
    (not (Common.get_force_cross_file_qualification ()))
    || ModPath.equal (base_mp mp) (base_mp wrapped)

let in_unmerged_wrapper r = in_unmerged_wrapper_named (Common.pp_global_name Type r) r

(** What a nested struct name was emitted for. A Rocq module has no
    [GlobRef.t], so it is identified by its module path instead -- which also
    covers the types declared inside it, since an eponymous record merged into
    the module struct is emitted as that same nested struct. *)
type nested_struct_owner = NSref of GlobRef.t | NSmodule of ModPath.t

(** C++ names of the structs emitted as members of an enclosing struct, mapped
    to every owner they stand for. Installed from the plan before anything is
    printed; the printer checks, under [CRANE_CHECK_IR], that it printed
    exactly these ({!printed_nested_struct}).

    A nested struct shadows any global-scope type of the same name for every
    unqualified lookup from inside its enclosing struct;
    {!Cpp_names.global_scope_qualifier_for} consults this through
    {!is_shadowed_global_name} to decide when the global one must be spelled
    [::Name]. One name can map to several references -- sibling modules may
    each declare a type [t] -- which is why the shadowed reference has to be
    identified rather than assumed. *)
let nested_struct_names : (string, nested_struct_owner list) Hashtbl.t =
  owned_table "nested_struct_names"

let nested_struct_owner_equal a b =
  match (a, b) with
  | NSref x, NSref y -> Common.globref_equal x y
  | NSmodule x, NSmodule y -> ModPath.equal x y
  | _ -> false

(** Whether [owner] is the nested struct that [r] is itself emitted as, either
    because [r] is that struct or because [r] is a member of the module that
    is. *)
let nested_struct_owner_covers r = function
  | NSref r' -> Common.globref_equal r r'
  | NSmodule mp -> ModPath.equal mp (modpath_of_r r)

(** The inductives a module's rendering promoted, under [CRANE_CHECK_IR]:
    the unit's planned ones must be exactly these. *)
let rendered_promotions : GlobRef.t list ref = State.cell State.Unit []

let rendered_promotion r = if Probe.checking () then rendered_promotions := r :: !rendered_promotions

(** The nested structs the printer printed, under [CRANE_CHECK_IR]: the
    unit's planned ones must be exactly these ({!printed_nested_struct}). *)
let printed_nested_structs : (string * nested_struct_owner) list ref = State.cell State.Unit []

(** Record that the printer printed [owner] as a nested struct named
    [name]. *)
let printed_nested_struct name owner =
  if Probe.checking () then printed_nested_structs := (name, owner) :: !printed_nested_structs

(** Record that [owner] was emitted as a nested struct named [name]. *)
let add_nested_struct_name name owner =
  let prev = Option.default [] (Hashtbl.find_opt nested_struct_names name) in
  if not (List.exists (nested_struct_owner_equal owner) prev) then
    Hashtbl.replace nested_struct_names name (owner :: prev)

(** Whether [r] is itself emitted as a struct nested inside another one --
    the case where its own name does not reach a use written outside that
    struct, so the reference needs the enclosing struct's qualifier. *)
let is_nested_struct_ref r =
  Hashtbl.fold
    (fun _name owners acc ->
      acc
      || List.exists
           (function NSref r' -> Common.globref_equal r r' | _ -> false)
           owners )
    nested_struct_names false

(** Whether [r], rendered unqualified as [name], is shadowed by some nested
    struct of the same name. A reference that is itself emitted as a nested
    struct is not shadowed: it is the shadower, and naming it [::name] would
    point at global scope, where it does not live. *)
let is_shadowed_global_name name r =
  match Hashtbl.find_opt nested_struct_names name with
  | Some owners ->
    not (List.exists (nested_struct_owner_covers r) owners)
  | None -> false

(** The struct a bystander [mp] keeps inside its collision wrapper: its
    module's name, which planning decided when it planned the wrapper
    ({!Common.decided_module_name}).  Read, never decided: a name first
    decided here would be decided by whatever wrote a reference first. *)
let bystander_struct_name mp =
  match Common.decided_module_name mp with
  | Some name -> name
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: the struct of the bystander " ++ str (ModPath.to_string mp) ++ str " has no decided name.")

(** The name [r], written [name] where its own module would write it, takes
    from outside a collision wrapper its module was put in.  Only constants
    and inductives: a [VarRef] is a lifted declaration, whose module path is
    the library's rather than any wrapper's, and a reference lifted out of the
    wrapper's struct to namespace scope does not have the struct as its
    scope.
    - A bare name is the one a use inside the reference's own module would
      say, and the wrapper's name alone does not get back to it: a bystander
      keeps its own struct, so the path runs through that struct too.
      Flattened children have no struct left to name, and for them the
      wrapper's name is the whole of it.
    - A qualified name, as its visibility qualifies it ([N::add]): a
      flattened child's own qualifier is replaced by the wrapper's ([BinNat]
      wrapping [N]); a bystander's stays, the wrapper's name going in front of
      it unless already there.  Under an ordinary wrapper ([List] wrapping
      [list]) the qualification is already complete. *)
let wrapper_qualify (r : GlobRef.t) (name : Cpp_name.t) : Cpp_name.t =
  match r with
  | GlobRef.VarRef _ -> name
  | _ when Module_plan.is_namespace_scope_ref r -> name
  | _ -> (
    let mp = modpath_of_r r in
    match (Module_plan.wrapper mp, name) with
    | None, _ | _, Cpp_name.Foreign _ -> name
    | Some (struct_name, role), Cpp_name.Name {scopes = []; base} ->
      let through_child =
        if role = Module_plan.Bystander then [Cpp_name.Class (bystander_struct_name mp)]
        else []
      in
      Cpp_name.name (Cpp_name.Class struct_name :: through_child) base
    | Some (_, Module_plan.Flattened), Cpp_name.Name {scopes = Cpp_name.Global :: _; _} -> name
    | Some (struct_name, Module_plan.Flattened), Cpp_name.Name {scopes = _ :: inner; base} ->
      Cpp_name.name (Cpp_name.Class struct_name :: inner) base
    | Some (struct_name, Module_plan.Bystander), Cpp_name.Name {scopes = first :: _; _} ->
      if first <> Cpp_name.Global && String.equal (Cpp_name.scope_text first) struct_name then name
      else Cpp_name.within (Cpp_name.Class struct_name) name
    | Some _, _ -> name )

(** The candidate a function the render meets is as a method of [epon_ref]
    ({!Method_registry.planned_candidate}). *)
let planned_method_candidate epon_ref func_ref body ty =
  Method_registry.planned_candidate (get_method_registry ()) epon_ref func_ref body ty

(** Check if a function is registered as a method, returning its eponymous type
    and this position if so. *)
let is_registered_method (func_ref : GlobRef.t) : (GlobRef.t * int) option =
  Method_registry.is_registered_method (get_method_registry ()) func_ref

(** The number of value parameters a registered method takes, receiver
    included; [0] when unknown. *)
let lookup_method_arity (func_ref : GlobRef.t) : int =
  Method_registry.lookup_arity (get_method_registry ()) func_ref

(** Look up the inductive's type variable positions (0-based indices into the
    function's tys list) for a registered method. These positions correspond to
    the inductive's template params which are already deducible from the
    receiver object and should be omitted from explicit template arguments in
    method calls. *)
let lookup_method_ind_tvar_positions (func_ref : GlobRef.t) : int list =
  Method_registry.lookup_ind_tvar_positions (get_method_registry ()) func_ref

(** The type of a registered method's receiver, given the type arguments [tys]
    the reference was instantiated at.  The receiver's own template arguments
    are exactly those of [tys] sitting at
    {!lookup_method_ind_tvar_positions} — the same correspondence that lets a
    call site drop them from the explicit template arguments, read in the
    other direction. *)
let method_receiver_cpp_type (func_ref : GlobRef.t)
    (tys : Minicpp.cpp_type list) : Minicpp.cpp_type option =
  match is_registered_method func_ref with
  | None -> None
  | Some (epon_ref, _) ->
    let positions = lookup_method_ind_tvar_positions func_ref in
    let ind_tys = List.filteri (fun i _ -> List.mem i positions) tys in
    (* Every one of the receiver's template parameters has to be recovered:
       an inductive spelled with too few is not a type. *)
    if List.length ind_tys <> Table.get_ind_nb_tparams epon_ref then None
    else Some (Minicpp.Tglob (epon_ref, ind_tys, []))

(** Whether a registered method's return type is erased to [std::any] (or
    [bsl::any]). *)
let method_returns_any (func_ref : GlobRef.t) : bool =
  Method_registry.method_returns_any (get_method_registry ()) func_ref

(** Eponymous records across modules. When a module M contains a record with
    the same name (e.g., module CHT with record CHT), the record fields are
    merged directly into the module struct. This avoids C++ name conflicts where
    both the module and record would have the same name.

    {!eponymous_record} only covers the module being rendered; type
    references from other modules need to know how to render the type name
    too, or a reference to CHT from another module would generate
    "CHT::cHT" instead of just "CHT".  That unit-wide answer is planned in
    {!Module_plan.is_eponymous_record}, which {!Cpp_names.inductive_type_name}
    reads. *)

(** Track current structure's declarations for finding methods from sibling
    modules. When processing a module like List inside tree.v, we need to also
    scan sibling declarations (like app) that are from the same Rocq module. *)
let current_structure_decls : (Label.t * Miniml.ml_structure_elem) list ref =
  owned_list ~census:false "current_structure_decls"

(** [promoted_inductives] lives in {!Table} but is reset and censused here,
    since this is the module that fills it. *)
let () =
  on_reset (fun () -> Ref.User.Tbl.clear promoted_inductives);
  Table.register_census "promoted_inductives" (fun () ->
      Ref.User.Tbl.length promoted_inductives )

(** Reset all state owned by this module, so that one extraction in a process
    cannot affect the next.  Every cell created by {!owned_table},
    {!owned_list} or {!owned_ref} is emptied; the rest is state other modules
    own that only this one knows to reset. *)
let reset_cpp_state () = State.reset State.Extraction

(** Check if a function is a projection for the eponymous record. Such
    projections are redundant when the record fields are merged into the module
    struct. *)
let is_eponymous_record_projection r =
  match !eponymous_record with
  | None -> false
  | Some (epon_ref, _, _) ->
    if Table.is_projection r then
      let ip, _arity = Table.projection_info r in
      (* Check if this projection's inductive matches the eponymous record *)
      globref_equal (GlobRef.IndRef ip) epon_ref
    else
      false

(** Whether a projection is suppressed: it is not a higher-order projection,
    so it is not rendered as a standalone function. *)
let is_suppressed_projection r =
  Table.is_projection r && not (Table.is_higher_order_projection r)

(** Filter a Dfix group, removing entries that are inline customs, registered
    methods (every method candidate is one), eponymous record projections, or
    suppressed projections: what is left is rendered directly. *)
let filter_dfix fds =
  List.filter
    (fun {Miniml.fd_ref = x; _} ->
      (not (is_inline_custom x))
      && is_registered_method x = None
      && (not (is_eponymous_record_projection x))
      && not (is_suppressed_projection x) )
    fds
