#ifndef INCLUDED_FIX_ESCAPE_CAPTURE
#define INCLUDED_FIX_ESCAPE_CAPTURE

#include "fn.h"
#include <cstdint>
#include <utility>

struct FixEscapeCapture {
  /// A local fixpoint that captures a function parameter and is returned
  /// in a pair. The fixpoint's & capture creates a dangling reference
  /// to the captured parameter after the enclosing function returns.
  static std::pair<uint64_t, crane::fn<uint64_t(uint64_t)>>
  make_pair_fn(uint64_t base);
  /// Invokes the escaped fixpoint — use-after-free if & capture.
  static constexpr uint64_t test_pair = UINT64_C(8);
  /// Same pattern with a non-recursive local fixpoint to isolate the
  /// capture issue from self-reference.
  static std::pair<uint64_t, crane::fn<uint64_t(uint64_t)>>
  make_pair_fn2(uint64_t base);

  static constexpr uint64_t test_pair2 = UINT64_C(18);
};

#endif // INCLUDED_FIX_ESCAPE_CAPTURE
