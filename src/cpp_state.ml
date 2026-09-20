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

(** Mutable state and utility functions for C++ code generation.

    This module holds all global mutable state (render context, hashtables,
    refs) used across the C++ pretty-printer, along with small utility functions
    that depend on that state. Centralising state here avoids circular
    dependencies between the other cpp_* modules. *)

open Pp
open CErrors
open Names
open ModPath
open Table
open Miniml
open Modutil
open Common
open Minicpp

(** {2 Pp box shadows}

    Since all output is reformatted by clang-format, the Pp box-layout algorithm
    is wasted work. Shadow h/v/hov with identity to skip box construction while
    keeping the same Pp.t type. *)

(** Shadow horizontal box constructor with identity. *)
let h x = x

(** Shadow vertical box constructor with identity. *)
let v _ x = x

(** Shadow horizontal-or-vertical box constructor with identity. *)
let hov _ x = x

(** {2 Owned cells}

    Every mutable cell this module owns is created by one of the constructors
    below, which enrol it in {!reset_cpp_state} and in {!Table.census} at the
    point it is defined.  Those two used to be hand-written lists naming the
    same set of cells from two hundred lines away, and they had already drifted
    apart; a cell that exists but is in neither list is now unrepresentable. *)

(** How to empty each owned cell, innermost-defined first.  Order is immaterial:
    the actions are independent. *)
let owned_cells : (unit -> unit) list ref = ref []

let on_reset f = owned_cells := f :: !owned_cells

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

(** The method registry is created once per extraction pass by scanning the full
    ml_structure. It replaces the old global_method_registry and
    methods_returning_any hashtables. Queries go through get_method_registry().
*)
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

(** Pre-computed name resolution cache — populated once per extraction pass.
    Queries go through get_name_cache(). *)
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
      "persistent_array";
      (* Macros the C standard headers define.  The preprocessor runs before
         any scope, so a declaration spelled like one is rewritten before the
         compiler sees it -- [static Request alloca(Nat, Nat, bool)] against
         <alloca.h> is "too many arguments provided to function-like macro".
         Only the spelling the header uses is reserved; the case-folded forms
         are separate names to the preprocessor. *)
      "alloca";
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
    ]
    Id.Set.empty

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

(** Pretty-print a comment with OCaml-style delimiters. *)
let pp_comment s = str "(* " ++ hov 0 s ++ str " *)"

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

(** {2 The pretty-printer for C++ syntax} *)

(* ============================================================================
   Render context — mutable state tracking the rendering position. These refs
   are saved/restored around sub-renders using with_render_ctx.
   ============================================================================ *)

(** Consolidated render context state: where in the output the printer
    currently is.

    The record is immutable and the mutability lives in the one {!render_ctx}
    ref, so saving and restoring a context around a sub-render is total --
    [let saved = !render_ctx in ... ; render_ctx := saved] cannot forget a
    field, whatever fields are added later. *)
type render_ctx = {
  (* Inside a struct body? Affects qualification of nested type references. *)
  rc_in_struct : bool;
  (* TypeClass concepts already emitted for the current module? *)
  rc_concepts_hoisted : bool;
  (* Current struct name for qualifying out-of-struct definitions *)
  rc_struct_name : Pp.t option;
  (* Current struct's ModPath for ModPath-based qualification checks. Needed
     when the C++ struct name differs from the Rocq module path. *)
  rc_struct_mp : ModPath.t option;
  (* Inside a template struct (functor)? Affects typename keyword insertion. *)
  rc_in_template : bool;
}

(** The context at the start of a file: file scope, outside every struct. *)
let initial_render_ctx =
  {
    rc_in_struct = false;
    rc_concepts_hoisted = false;
    rc_struct_name = None;
    rc_struct_mp = None;
    rc_in_template = false;
  }

(** Global render context state. *)
let render_ctx = owned_ref initial_render_ctx

(** Accumulator for nested module type concepts that must be hoisted out of
    requires bodies *)
let hoisted_concept_defs : Pp.t list ref = owned_list "hoisted_concept_defs"

(** Concepts from typeclasses declared inside a module.  A concept may only
    appear at namespace scope, so one declared in a module -- which is emitted
    as a struct -- cannot stay where it was written; it is collected here and
    emitted at file scope instead. *)
let file_scope_concepts : Pp.t list ref = owned_list "file_scope_concepts"

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

(** The concepts the struct now being rendered has held back: their
    declarations come after it, so neither a [requires] clause nor a
    [static_assert] inside it may name them yet. *)
let held_back_concepts : held_concept list ref =
  owned_list ~census:false "held_back_concepts"

(** Whether a concept is one the current frame is holding back. *)
let is_held_back_in held_back c =
  List.exists (held_concept_equal c) held_back

(** Assertions deferred out of the struct being rendered.  Each entry is the
    concept held back, its name, and the asserted subject -- qualified as far
    as the frames it has passed through; the frame that held the concept back
    emits it. *)
let deferred_concept_asserts : (held_concept * Pp.t * Pp.t) list ref =
  owned_list ~census:false "deferred_concept_asserts"

(** [with_render_ctx upd f] renders [f] in the context [upd] derives from the
    current one, and puts the enclosing context back on the way out however [f]
    leaves -- returning or raising.

    Every context change goes through this, so that no caller writes the
    save/set/restore by hand: an omitted restore does not fail, it silently
    renders the rest of the file as though it were still inside the struct that
    has just closed. *)
let with_render_ctx (upd : render_ctx -> render_ctx) (f : unit -> 'a) : 'a =
  let saved = !render_ctx in
  render_ctx := upd saved;
  Fun.protect ~finally:(fun () -> render_ctx := saved) f

(** Track definitions rendered as function accessors (Meyers singletons) instead
    of static inline variables, due to template static init ordering. Stores
    both (modpath, label) pairs for direct matching and canonical KerNames for
    cross-functor matching. [non_accessor_labels] tracks labels that are
    also used by NON-Meyers-singleton definitions, to prevent false positives
    when doing label-only fallback matching. *)
let template_static_accessors : (ModPath.t * Label.t) list ref =
  owned_list "template_static_accessors"
let template_static_accessor_kns : (KerName.t, unit) Hashtbl.t =
  owned_table "template_static_accessor_kns"
let non_accessor_labels : (Label.t, unit) Hashtbl.t =
  owned_table "non_accessor_labels"

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

(** {!register_template_static_accessor} for a global reference, which also
    records the constant's kername for cross-functor matching. *)
let register_template_static_accessor_ref r =
  register_template_static_accessor (Table.modpath_of_r r) (Table.label_of_r r);
  match r with
  | GlobRef.ConstRef c ->
    Hashtbl.replace template_static_accessor_kns (Constant.canonical c) ()
  | _ -> ()

(** Maps applied module paths to their functor source modpaths. E.g.,
    NatWrapper's modpath -> Wrapper's modpath. Populated when processing
    MEapply. *)
let functor_app_sources : (ModPath.t, ModPath.t) Hashtbl.t =
  owned_table "functor_app_sources"

(** Track eponymous type info for method generation. When a module M contains an
    inductive type m (lowercase of M), functions taking shared_ptr<m> as first
    arg become methods on m. *)
let eponymous_type_ref : GlobRef.t option ref = owned_ref None

(** Set during module rendering when the eponymous inductive should be promoted
    into the module struct. cpp_ind.ml checks this to render fields flat instead
    of a wrapping struct. *)
let eponymous_promote_ref : GlobRef.t option ref = owned_ref None

(** Accumulator for non-inductive definitions that should be emitted after the
    promoted template struct at file scope. *)
let eponymous_deferred : Pp.t ref = owned_ref (Pp.mt ())


(** Whether the promoted inductive needs enable_shared_from_this. Captured
    during flat rendering in cpp_ind.ml, consumed by the MEstruct wrapper in
    cpp.ml. *)
let eponymous_promote_sft : bool ref = owned_ref false

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

    The render context proper lives in one record behind {!render_ctx}, so
    {!with_render_ctx} restores it in full.  The state below could not join it
    -- it is read in a dozen modules under the names it already has -- so it
    stays in its own refs and is bracketed instead of inlined. *)

(** A mutable cell a scope saves and restores, with its contents' type hidden
    so that cells of different types can be listed together. *)
type saver = Saver : 'a ref -> saver

(** [with_saved cells f] runs [f] and puts every cell in [cells] back the way
    it found it, however [f] leaves -- returning or raising.

    The point is to name the cells a scope owns in one place.  Five of the
    six restores this replaced were written out at the end of a branch some
    hundreds of lines below the save, and none of them survived an
    exception. *)
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

    {!render_ctx} is not here -- entering a module changes it rather than
    merely shadowing it, which is {!with_render_ctx}'s job. *)
let module_frame_cells =
  [
    Saver eponymous_type_ref;
    Saver eponymous_record;
    Saver method_candidates;
    Saver held_back_concepts;
  ]

(** [with_module_frame f] renders [f] as a module frame: it starts with no
    eponymous type, no eponymous record and no method candidates of its own,
    and leaves the enclosing frame's untouched.  [held_back_concepts] carries
    over, since a concept the enclosing struct is holding back is still
    unusable inside a nested one. *)
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

(** [collecting acc f] runs [f] with the accumulator [acc] emptied and returns
    what [f] pushed onto it, in push order, alongside [f]'s result.  The
    enclosing contents are put back on the way out however [f] leaves.

    An accumulator differs from the cells above in that the enclosing scope
    wants to {e see} what the nested one produced; restoring it is not enough
    and reading it after the restore is too late. *)
let collecting acc f =
  let outer = !acc in
  acc := [];
  Fun.protect
    ~finally:(fun () -> acc := outer)
    (fun () ->
      let v = f () in
      (List.rev !acc, v) )

(* NOTE: The global method registry has moved to Method_registry. Lookups go
   through get_method_registry(). *)

(** Resolved standard library names — computed once per extraction pass from
    Table.std_lib() and queried everywhere instead of 20+ scattered checks. *)
type std_names = {
  shared_ptr : string; (* "std::shared_ptr" or "bsl::shared_ptr" *)
  make_shared : string; (* "std::make_shared" or "bsl::make_shared" *)
  move : string; (* "std::move" or "bsl::move" *)
  forward : string; (* "std::forward" or "bsl::forward" *)
  any_cast : string; (* "std::any_cast" or "bsl::any_cast" *)
  logic_error : string; (* "std::logic_error" or "bsl::logic_error" *)
  ns : string; (* "std" or "bsl" — general prefix *)
  str_suffix : string; (* "s" or "_s" — string literal suffix *)
  same_as : string; (* "std::same_as" or "same_as" *)
  declval : string; (* "std::declval" or "bsl::declval" *)
  convertible_to : string; (* "std::convertible_to" or "convertible_to" *)
  holds_alternative : string; (* "std::holds_alternative" or "bsl::holds_alternative" *)
  get_if : string; (* "std::get_if" or "bsl::get_if" *)
  get : string; (* "std::get" or "bsl::get" *)
  enable_from_this : string; (* enable_shared_from_this base, or crane::enable_rc_from_this *)
}

let default_std_names =
  {
    shared_ptr = "std::shared_ptr";
    make_shared = "std::make_shared";
    move = "std::move";
    forward = "std::forward";
    any_cast = "std::any_cast";
    logic_error = "std::logic_error";
    ns = "std";
    str_suffix = "s";
    same_as = "std::same_as";
    declval = "std::declval";
    convertible_to = "std::convertible_to";
    holds_alternative = "std::holds_alternative";
    get_if = "std::get_if";
    get = "std::get";
    enable_from_this = "std::enable_shared_from_this";
  }

(** Global reference to standard library names, initialized by init_std_names. *)
let std_names : std_names ref = ref default_std_names

let mk_std_names prefix =
  match prefix with
  | "bsl::" ->
    let p = prefix in
    { shared_ptr = p ^ "shared_ptr"; make_shared = p ^ "make_shared";
      move = p ^ "move"; forward = p ^ "forward";
      any_cast = p ^ "any_cast"; logic_error = p ^ "logic_error";
      ns = "bsl"; str_suffix = "_s";
      same_as = "same_as"; declval = p ^ "declval";
      convertible_to = "convertible_to";
      holds_alternative = p ^ "holds_alternative";
      get_if = p ^ "get_if"; get = p ^ "get";
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

(** Inline check: is a term a typeclass instance? Replaces
    is_typeclass_instance. A term is a typeclass instance if its return type is
    a Tglob referencing a typeclass.
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

(** Wrapper module table: maps ModPath.t of imported modules to their
   wrapper struct name. When a module like Stdlib.Init.Nat is wrapped
   in 'struct Nat { ... }', this table records the mapping so that
   references to functions in that module get properly qualified. *)
let wrapper_module_table : (ModPath.t, string) Hashtbl.t =
  owned_table "wrapper_module_table"

(** Collision wrapper table: tracks modpaths that were registered as
    collision-wrapped (i.e., a child module whose name collides with a global
    inductive, wrapped into a parent struct). For these, wrapper_qualify_name
    strips the child qualifier. *)
let collision_wrapper_table : (ModPath.t, unit) Hashtbl.t =
  owned_table "collision_wrapper_table"

(** The name each type class's concept is emitted under, for the classes whose
    own name does not settle it: a concept is declared at file scope, so two
    classes called [C] in different modules are told apart by their module's
    name.  Decided by the structure analysis before any
    rendering, and read by {!Cpp_names.concept_name_of_ref}. *)
let concept_name_table : (GlobRef.t, string) Hashtbl.t =
  owned_table "concept_name_table"

(** Global-scope enum table: tracks enum inductives that were rendered at global
    scope (not inside any struct). Used to avoid incorrect struct qualification
    in .cpp files. *)
let global_scope_enum_table : (GlobRef.t, unit) Hashtbl.t =
  owned_table "global_scope_enum_table"

(** The type names a wrapper struct's module contributes to C++ {i global}
    scope rather than to the struct.

    A module forced into a wrapper struct by a name collision does not take
    all of its declarations with it.  A type alias stays outside as
    [using T = ...;], because C++ puts it there; a type class instance is
    lifted out deliberately, because an instance is named from wherever its
    class is used and a concept's template argument is a type, not a member of
    whatever module happened to declare it.  Either way the wrapper struct
    does not declare the name, and {!Cpp_names.struct_qualifier_for} must not
    write [Wrapper::] in front of it in the [.cpp].

    Asking where the name was {i emitted} is the only question that answers
    this; where it was {i declared} in Rocq says the opposite, and says it
    confidently.

    {b Lifecycle:} populated from {!Structure_analysis}'s module layout before
    any rendering begins -- which is what makes it safe to read from a [.cpp]
    body printed long before the [.h] declares the name.  Queried in
    [cpp_names.ml] for name qualification; cleared by [reset_cpp_state]. *)
let global_scope_type_table : (GlobRef.t, unit) Hashtbl.t =
  owned_table "global_scope_type_table"

let register_global_scope_type r = Hashtbl.replace global_scope_type_table r ()

let is_global_scope_type r = Hashtbl.mem global_scope_type_table r

(** Pending wrapper declarations: maps a Dnspace struct name (e.g., "Nat") to
    pre-rendered forward declarations (specs) that should be injected into that
    struct. Full definitions are rendered separately in PASS 3 after all types
    are defined. Populated during do_struct_with_decl_tracking PASS 1. Consumed
    during Dnspace rendering in PASS 2. *)
let pending_wrapper_decls : (string, Pp.t) Hashtbl.t =
  owned_table "pending_wrapper_decls"

(** Set of wrapper struct names that have pending declarations and thus cannot
    be merged. Populated alongside pending_wrapper_decls during PASS 1. Used
    during type/expression rendering to decide between merged (List<A>) and
    unmerged (List::list<A>) name formats. Not consumed during rendering. *)
let unmerged_wrappers : (string, unit) Hashtbl.t =
  owned_table "unmerged_wrappers"

(** What a nested struct name was emitted for. A Rocq module has no
    [GlobRef.t], so it is identified by its module path instead -- which also
    covers the types declared inside it, since an eponymous record merged into
    the module struct is emitted as that same nested struct. *)
type nested_struct_owner = NSref of GlobRef.t | NSmodule of ModPath.t

(** C++ names of the structs emitted as members of an enclosing struct, mapped
    to every owner they stand for. Recorded by the struct printer, which is
    where the name is actually rendered, so the two cannot drift.

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

(** Maps capitalized inductive names to their ModPaths across all modules.
    Pre-populated in do_struct_with_decl_tracking before code generation. Used
    to detect module-inductive name collisions (e.g., N/Z appearing as both an
    inductive from BinNums and a module from BinNat). *)
let global_inductive_names : (string, ModPath.t) Hashtbl.t =
  owned_table "global_inductive_names"

(** Whether a use of [r] is spelled with a wrapper struct's name in front of
    it.

    The qualifier is a struct's, so naming [r] is name lookup {e into} that
    struct and needs it complete -- which is the one thing a position above the
    structs cannot supply, a forward declaration being all that is available
    there.  An inductive that is not in a wrapper module is spelled bare
    however deeply it nests in the IR, and needs only to have been declared.

    The two exceptions are {!wrapper_qualify_name}'s own: a lifted declaration
    is a [VarRef] and has no module, and something lifted to namespace scope is
    no longer in the struct whatever its module path says. *)
let is_wrapper_qualified (r : GlobRef.t) : bool =
  match r with
  | GlobRef.VarRef _ -> false
  | _ when Common.is_namespace_scope_ref r -> false
  | _ -> Hashtbl.mem wrapper_module_table (modpath_of_r r)

(** Check if a GlobRef belongs to a wrapper module and return the qualified
    name. If the reference's module path matches a wrapper module, prepend the
    struct name. Only qualify ConstRef globals (actual Rocq constants from
    modules). VarRef globals are lifted declarations (like _foo_aux) that should
    not be qualified with a wrapper struct name — their modpath comes from
    Lib.make_kn which reflects the current library, not the wrapper module.
    @param r the global reference whose module path is checked
    @param name the unqualified (or partially qualified) C++ name string
    @return [name] unchanged if [r] is not in a wrapper module; otherwise
      ["StructName::name"] (or the collision-stripped variant for
      collision-wrapped modules) *)
let wrapper_qualify_name (r : GlobRef.t) (name : string) : string =
  match r with
  | GlobRef.VarRef _ -> name (* Lifted declarations: never qualify *)
  | _ when Common.is_namespace_scope_ref r ->
    (* Lifted out of the wrapper's struct, so the struct is not its scope. *)
    name
  | _ ->
    let mp = modpath_of_r r in
    ( match Hashtbl.find_opt wrapper_module_table mp with
    | Some struct_name when not (String.contains name ':') ->
      struct_name ^ "::" ^ name
    | Some struct_name when String.contains name ':' ->
      (* Name is already qualified (e.g., "N::add" from visibility stack). Only
         strip the child qualifier for collision-wrapped entries (e.g., BinNat
         wrapping N). For normal wrappers (e.g., List wrapping list), keep the
         full qualification. *)
      if Hashtbl.mem collision_wrapper_table mp then
        match
          String.index_opt name ':'
        with
        | Some colon_pos
          when colon_pos > 0
               && colon_pos + 1 < String.length name
               && name.[colon_pos + 1] = ':' ->
          let func_part =
            String.sub name (colon_pos + 2) (String.length name - colon_pos - 2)
          in
          struct_name ^ "::" ^ func_part
        | _ -> name
      else
        name
    | _ -> name )

(** Register a method with the method registry.
    @param func_ref the global reference of the function being registered as a method
    @param epon_ref the global reference of the eponymous inductive type on which
      the method is defined (i.e., the C++ [this] type)
    @param this_pos 0-based index of the argument whose type is [epon_ref]
    @param ind_tvar_positions 0-based indices into the function's type variable
      list that correspond to the inductive's own template parameters; these are
      deducible from the receiver and omitted from explicit template arguments *)
let register_method
    (func_ref : GlobRef.t)
    (epon_ref : GlobRef.t)
    (this_pos : int)
    ?(ind_tvar_positions : int list = [])
    () =
  Method_registry.register_method
    (get_method_registry ())
    func_ref
    epon_ref
    this_pos
    ~ind_tvar_positions

(** Check if a function qualifies as a method on [epon_ref] and register it
    if so.  Single entry point replacing the manual
    [find_epon_arg_pos] + [body_safe_for_method] + [register_method] +
    [add_candidate] sequence.
    @param epon_ref the eponymous inductive type that [func_ref] might become a method on
    @param func_ref the global reference of the function being tested
    @param body the Miniml AST body of the function
    @param ty the Miniml type of the function *)
let try_register_method epon_ref func_ref body ty =
  Method_registry.try_register_method
    (get_method_registry ()) epon_ref func_ref body ty

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

(** Register that a method returns std::any or bsl::any. *)
let register_method_returns_any (func_ref : GlobRef.t) =
  Method_registry.register_method_returns_any (get_method_registry ()) func_ref

(** Record the C++ types a registered method's non-receiver parameters were
    declared at, in declaration order.  Called from declaration generation,
    which is where those types are decided; the printer reads them back when it
    has to spell a forwarding lambda for the method in value position. *)
let register_method_param_cpp_types (func_ref : GlobRef.t)
    (tys : Minicpp.cpp_type list) =
  Method_registry.register_method_param_cpp_types
    (get_method_registry ()) func_ref tys

(** The C++ types of a registered method's non-receiver parameters, or [None]
    when its declaration has not been generated yet: generation and printing
    interleave, so a use site can be printed before the declaration it names
    and must have something to fall back on. *)
let method_param_cpp_types (func_ref : GlobRef.t) :
    Minicpp.cpp_type list option =
  Method_registry.lookup_method_param_cpp_types (get_method_registry ()) func_ref

(** Check if a method is registered as returning std::any or bsl::any. *)
let method_returns_any (func_ref : GlobRef.t) : bool =
  Method_registry.method_returns_any (get_method_registry ()) func_ref

(** Global registry of eponymous records. When a module M contains a record with
    the same name (e.g., module CHT with record CHT), the record fields are
    merged directly into the module struct. This avoids C++ name conflicts where
    both the module and record would have the same name.

    This registry is global (not per-module) because type references from OTHER
    modules need to know how to render the type name. Without this registry, a
    reference to CHT from another module would incorrectly generate "CHT::cHT"
    instead of just "CHT".

    See also: pp_inductive_type_name which uses this registry for type name
    rendering. *)
let global_eponymous_record_registry : (GlobRef.t, unit) Hashtbl.t =
  owned_table "global_eponymous_record_registry"

(** Reverse index for {!get_containing_eponymous_struct}: maps a module path to
    the eponymous record declared in it. Kept in sync by
    {!register_eponymous_record} so the lookup is O(1) instead of scanning the
    whole registry on every call. There is at most one eponymous record per
    module (a record sharing its module's name), so a single-valued index is
    exact. Reset alongside [global_eponymous_record_registry]. *)
let eponymous_record_by_modpath : (ModPath.t, GlobRef.t) Hashtbl.t =
  owned_table "eponymous_record_by_modpath"

(** Register a record as eponymous with its containing module. *)
let register_eponymous_record (record_ref : GlobRef.t) =
  Hashtbl.replace global_eponymous_record_registry record_ref ();
  match record_ref with
  | GlobRef.IndRef (ind, _) ->
    Hashtbl.replace
      eponymous_record_by_modpath
      (Names.MutInd.modpath ind)
      record_ref
  | _ -> ()

(** Check if a GlobRef is registered as an eponymous record. *)
let is_eponymous_record_global (r : GlobRef.t) : bool =
  Hashtbl.mem global_eponymous_record_registry r

(** Check if a constant (function) is inside an eponymous template module.
    Returns Some record_ref if the function is inside a module whose name
    matches a registered eponymous record. This is used to correctly generate
    StructName<Args>::funcName() instead of StructName::funcName<Args>(). *)
let get_containing_eponymous_struct (r : GlobRef.t) : GlobRef.t option =
  match r with
  | GlobRef.ConstRef kn ->
    (* O(1) lookup by the constant's module path against the reverse index. *)
    Hashtbl.find_opt eponymous_record_by_modpath (Names.Constant.modpath kn)
  | _ -> None

(** Track current structure's declarations for finding methods from sibling
    modules. When processing a module like List inside tree.v, we need to also
    scan sibling declarations (like app) that are from the same Rocq module. *)
let current_structure_decls : (Label.t * Miniml.ml_structure_elem) list ref =
  owned_list ~census:false "current_structure_decls"

(** [promoted_inductives] lives in {!Table} but is reset and censused here,
    since this is the module that fills it. *)
let () =
  on_reset (fun () -> Hashtbl.clear promoted_inductives);
  Table.register_census "promoted_inductives" (fun () ->
      Hashtbl.length promoted_inductives )

(** Reset all state owned by this module, so that one extraction in a process
    cannot affect the next.  Every cell created by {!owned_table},
    {!owned_list} or {!owned_ref} is emptied; the rest is state other modules
    own that only this one knows to reset. *)
let reset_cpp_state () =
  List.iter (fun empty -> empty ()) !owned_cells;
  Doc_comments.reset ();
  Common.reset_ctor_field_names ();
  Table.reset_demands ();
  Table.reset_main_function ()

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

(** Check if a projection should be suppressed (not rendered as higher-order).
*)
let is_suppressed_projection r =
  Table.is_projection r && not (Table.is_higher_order_projection r)

(** Filter a Dfix group, removing entries that are inline customs, method
    candidates (local or globally registered), eponymous record projections, or
    suppressed projections. Returns the three filtered arrays (refs, bodies,
    types).
    @param rv array of global references for each definition in the Dfix group
    @param defs array of Miniml AST bodies parallel to [rv]
    @param typs array of Miniml types parallel to [rv]
    @return a triple [(rv', defs', typs')] containing only the entries that
      should be rendered directly *)
let filter_dfix rv defs typs =
  let is_method_candidate x =
    List.exists
      (fun (r', _, _, _) -> globref_equal x r')
      !method_candidates
  in
  let is_global_method x = is_registered_method x <> None in
  let filter =
    Array.to_list
      (Array.map
         (fun x ->
           (not (is_inline_custom x))
           && (not (is_method_candidate x))
           && (not (is_global_method x))
           && (not (is_eponymous_record_projection x))
           && not (is_suppressed_projection x) )
         rv )
  in
  let filter_array mask arr =
    let lst = Array.to_list arr in
    let filtered =
      List.filter_map
        (fun (keep, x) -> if keep then Some x else None)
        (List.combine mask lst)
    in
    Array.of_list filtered
  in
  (filter_array filter rv, filter_array filter defs, filter_array filter typs)
