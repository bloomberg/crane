(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

let rc = "crane::rc"
let make_rc = "crane::make_rc"
let enable_rc_from_this = "crane::enable_rc_from_this"
let make_rc_reusing = "crane::make_rc_reusing"
let make_rc_reusing_unchecked = "crane::make_rc_reusing_unchecked"
let reuse_step = "crane::reuse_step"
let arena_alloc = "crane::arena_alloc"
let arena_shared_alloc = "crane::arena_shared_alloc"
let arena_make_shared = "crane::arena_make_shared"
let any_cast = "crane_any_cast"
let erase_fn = "crane_erase_fn"
let erase_global = "crane_erase_global"
let call_erased = "crane_call_erased"
let convert = "crane_convert"
let convertible = "crane_convertible"
let container_cast = "crane_container_cast"
let small_vector = "crane::small_vector"
let lazy_ = "crane::lazy"
let fn = "crane::fn"
let fn_header = "fn.h"
let obj = "crane::obj"
let obj_cast = "crane::any_cast"
let obj_header = "obj.h"
let lazy_header = "lazy.h"
let erasure_header = "crane_fn.h"
let itree_header = "crane_itree.h"
let rebind = "crane::rebind_t"
let variant = "crane::variant"
let variant_header = "crane_variant.h"
let shared_variant = "crane::shared_variant"
let shared_box = "crane::shared_box"
let shared_or = "crane::shared_or_t"
let shared_variant_header = "shared_variant.h"
let field = "crane::field"
let field_header = "field.h"

(* [CRANE_COUNT_RC]: the measurement-only counting shared pointer (count_rc.h). *)
let counting_ptr = "crane::counting_ptr"
let make_counting = "crane::make_counting"

let raw = "crane_raw"

type helper =
  | Make_rc_reusing_unchecked
  | Reuse_step
  | Raw
  | Unbox_field
  | Apply2
  | Constant

let name = function
  | Constant -> "crane::constant"
  | Apply2 -> "crane::apply2"
  | Make_rc_reusing_unchecked -> make_rc_reusing_unchecked
  | Raw -> raw
  | Unbox_field -> "crane::unbox"
  | Reuse_step -> reuse_step
