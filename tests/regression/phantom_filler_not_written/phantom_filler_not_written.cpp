#include "phantom_filler_not_written.h"

/// Counts n down in E', passing the cell along.
uint64_t PhantomFillerNotWritten::count_down(const std::shared_ptr<uint64_t> &c,
                                             uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    uint64_t r = count_down(c, n_);
    return (r + 1);
  }
}

uint64_t PhantomFillerNotWritten::run_count(const std::shared_ptr<uint64_t> &c,
                                            uint64_t n) {
  return count_down(c, n);
}
