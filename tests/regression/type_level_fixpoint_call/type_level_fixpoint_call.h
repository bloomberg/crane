#ifndef INCLUDED_TYPE_LEVEL_FIXPOINT_CALL
#define INCLUDED_TYPE_LEVEL_FIXPOINT_CALL

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>

/// A Fixpoint returning Type erases to std::any: a value of type ty 1
/// is stored as an erased callable and applied through the canonical
/// adapter.
struct TypeLevelFixpointCall {
  using ty = crane::obj;
  static inline const ty v1 =
      crane_erase_fn([](uint64_t n) { return (n + UINT64_C(1)); });
  static constexpr uint64_t go = UINT64_C(5);
};

#endif // INCLUDED_TYPE_LEVEL_FIXPOINT_CALL
