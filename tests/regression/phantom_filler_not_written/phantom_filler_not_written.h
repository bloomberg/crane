#pragma once

#include "obj.h"
#include <cstdint>
#include <memory>
#include <variant>

struct PhantomFillerNotWritten {
  /// Counts n down in E', passing the cell along.
  template <typename T1 = void, typename T2 = void>
  static uint64_t count_down(const std::shared_ptr<uint64_t> &c, uint64_t n) {
    if (n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n_ = n - 1;
      uint64_t r = count_down<crane::obj, crane::obj>(c, n_);
      return (r + 1);
    }
  }

  static uint64_t run_count(const std::shared_ptr<uint64_t> &c, uint64_t n);
};
