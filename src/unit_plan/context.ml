(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The context of one unit's extraction.  See [unit_context.mli]. *)

type std_names = {
  shared_ptr : string; (* "std::shared_ptr" or "bsl::shared_ptr" *)
  make_shared : string; (* "std::make_shared" or "bsl::make_shared" *)
  move : string; (* "std::move" or "bsl::move" *)
  forward : string; (* "std::forward", in either flavour: BDE has no [bsl::forward] *)
  logic_error : string; (* "std::logic_error" or "bsl::logic_error" *)
  ns : string; (* "std" or "bsl": general prefix *)
  string : string; (* "std::string" or "bsl::string" *)
  same_as : string; (* "std::same_as" or "same_as" *)
  declval : string; (* "std::declval", in either flavour *)
  convertible_to : string; (* "std::convertible_to" or "convertible_to" *)
  holds_alternative : string; (* "std::holds_alternative" or "bsl::holds_alternative" *)
  get_if : string; (* "std::get_if" or "bsl::get_if" *)
  get : string; (* "std::get" or "bsl::get" *)
  variant : string; (* "std::variant", "bsl::variant" or "crane::variant" *)
  variant_header : Base.Table.header; (* the header [variant] is declared in *)
  enable_from_this : string; (* enable_shared_from_this base, or crane::enable_rc_from_this *)
  unreachable : string; (* "std::unreachable" (C++23), or "crane::unreachable" where the build is older *)
  unreachable_header : Base.Table.header; (* the header [unreachable] is declared in *)
  placeholder : bool; (* an unread binding written [_] (C++26), or by its own name where the build is older *)
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
    variant_header = Base.Table.Standard "variant";
    enable_from_this = "std::enable_shared_from_this";
    unreachable = "std::unreachable";
    unreachable_header = Base.Table.Standard "utility";
    placeholder = true;
  }

type t = {
  config : Base.Table.unit_config;
  callables : Core_plan.Callable_abi.decided;
  modules : Core_plan.Module_plan.layout;
  pointer_fields : Core_plan.Pointer_fields.t;
  unmerged_wrappers : Names.ModPath.t CString.Map.t;
  accessors : Core_plan.Struct_plan.accessors;
  nested_structs : Core_plan.Struct_plan.nested_structs;
  promoted_inductives : Core.Ref.User.Set.t;
  instance_promoted_types : (Names.Id.t * Core.Type.t) list Names.GlobRef.Map.t;
  scopes : Core_plan.Scope_plan.bound;
  names : Core_plan.Name_resolution.t option;
  loops : Core_to_control.Loop_facts.t;
  std_names : std_names;
}

let make ~config =
  { config;
    callables = Core_plan.Callable_abi.undecided;
    modules = Core_plan.Module_plan.no_layout;
    pointer_fields = Core_plan.Pointer_fields.none;
    unmerged_wrappers = CString.Map.empty;
    accessors = Core_plan.Struct_plan.no_accessors;
    nested_structs = CString.Map.empty;
    promoted_inductives = Core.Ref.User.Set.empty;
    instance_promoted_types = Names.GlobRef.Map.empty;
    scopes = Core_plan.Scope_plan.none;
    names = None;
    loops = Core_to_control.Loop_facts.none;
    std_names = default_std_names }
let detached = make ~config:{Base.Table.concurrent = false}
let non_atomic_rc u = Base.Table.non_atomic_rc_for u.config
let count_rc u = Base.Table.count_rc_for u.config
let is_promoted_inductive u r = Core.Ref.User.Set.mem r u.promoted_inductives

let instance_promoted_types_of u r =
  match Names.GlobRef.Map.find_opt r u.instance_promoted_types with Some bindings -> bindings | None -> []

let recursion u = u.loops.recursion
let control u = u.loops.control
let loop_effects u = u.loops.effects
