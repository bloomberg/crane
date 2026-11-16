(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The context of one unit's extraction.  See [unit_context.mli]. *)

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

type t = {
  config : Table.unit_config;
  callables : Callable_abi.decided;
  modules : Module_plan.layout;
  pointer_fields : Pointer_fields.t;
  unmerged_wrappers : Names.ModPath.t CString.Map.t;
  accessors : Struct_plan.accessors;
  nested_structs : Struct_plan.nested_structs;
  promoted_inductives : Ref.User.Set.t;
  instance_promoted_types : (Names.Id.t * Core.Type.t) list Names.GlobRef.Map.t;
  scopes : Scope_plan.bound;
  names : Name_resolution.t option;
  loops : Loop_facts.t;
  std_names : std_names;
}

let make ~config =
  { config;
    callables = Callable_abi.undecided;
    modules = Module_plan.no_layout;
    pointer_fields = Pointer_fields.none;
    unmerged_wrappers = CString.Map.empty;
    accessors = Struct_plan.no_accessors;
    nested_structs = CString.Map.empty;
    promoted_inductives = Ref.User.Set.empty;
    instance_promoted_types = Names.GlobRef.Map.empty;
    scopes = Scope_plan.none;
    names = None;
    loops = Loop_facts.none;
    std_names = default_std_names }
let detached = make ~config:{Table.concurrent = false}
let non_atomic_rc u = Table.non_atomic_rc_for u.config
let count_rc u = Table.count_rc_for u.config
let is_promoted_inductive u r = Ref.User.Set.mem r u.promoted_inductives

let instance_promoted_types_of u r =
  match Names.GlobRef.Map.find_opt r u.instance_promoted_types with Some bindings -> bindings | None -> []

let recursion u = u.loops.recursion
let control u = u.loops.control
let loop_effects u = u.loops.effects
