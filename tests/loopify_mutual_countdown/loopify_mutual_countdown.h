#ifndef INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN
#define INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN

#include <utility>

struct LoopifyMutualCountdown {
  static bool even_countdown(uint64_t n);
  static bool odd_countdown(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN
