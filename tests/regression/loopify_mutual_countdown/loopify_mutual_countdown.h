#ifndef INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN
#define INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN

#include <utility>

struct LoopifyMutualCountdown {
  /// Loopification handles many self-recursive functions, but this probes a
  /// mutually recursive countdown.  The Rocq computation is total and uses only
  /// bounded numeric values in the C++ test.  With Set Crane Loopify., Crane
  /// still emits even_countdown and odd_countdown as ordinary mutually
  /// recursive C++ calls instead of a loop, so a deep countdown overflows the
  /// C++ stack.
  static bool even_countdown(uint64_t n);
  static bool odd_countdown(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN
