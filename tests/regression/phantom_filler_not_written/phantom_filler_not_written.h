#pragma once

#include <cstdint>
#include <memory>
#include <variant>

struct PhantomFillerNotWritten {
  /// Counts n down in E', passing the cell along.
  static uint64_t count_down(const std::shared_ptr<uint64_t> &c, uint64_t n);
  static uint64_t run_count(const std::shared_ptr<uint64_t> &c, uint64_t n);
};
