#include "loopify_filter_fn_ref.h"

/// A concrete predicate — will be passed as a function reference.
bool LoopifyFilterFnRef::is_positive(uint64_t n) {
  if (n <= 0) {
    return false;
  } else {
    uint64_t _x = n - 1;
    return true;
  }
}
