#ifndef INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN
#define INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LoopifyMutualCountdown {
  static bool even_countdown(const unsigned int n);
  static bool odd_countdown(const unsigned int n);
};

#endif // INCLUDED_LOOPIFY_MUTUAL_COUNTDOWN
