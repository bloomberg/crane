#include "phantom_filler_not_written.h"

uint64_t PhantomFillerNotWritten::run_count(const std::shared_ptr<uint64_t> &c,
                                            uint64_t n) {
  return count_down<std::monostate, void>(c, n);
}
