#pragma once

#include "obj.h"
#include <cstdint>

struct RocqBug4709 {
  enum class T { FOO };
  using foo = crane::obj;
  using ty = uint64_t;
  static inline const ty check = UINT64_C(42);
};
