#pragma once

#include <cstdint>
#include <todo_extract_constant_noninline_support.h>

struct TodoExtractConstantNoninline {
  static inline const uint64_t test_value = foreign_inc_impl(UINT64_C(4));
  static inline const uint64_t twice_value =
      foreign_inc_impl(foreign_inc_impl(UINT64_C(2)));
};
