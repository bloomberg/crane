#ifndef INCLUDED_TYPE_LEVEL_FIXPOINT_CALL
#define INCLUDED_TYPE_LEVEL_FIXPOINT_CALL

#include "crane_fn.h"
#include <any>
#include <functional>

struct TypeLevelFixpointCall {
  using ty = std::any;
  static inline const ty v1 =
      crane_erase_fn([](uint64_t n) { return (n + UINT64_C(1)); });
  static inline const uint64_t go =
      std::any_cast<uint64_t>(std::any_cast<std::function<std::any(std::any)>>(
          v1)(std::any(UINT64_C(4))));
};

#endif // INCLUDED_TYPE_LEVEL_FIXPOINT_CALL
