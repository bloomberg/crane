#ifndef INCLUDED_ROCQ_BUG_10796
#define INCLUDED_ROCQ_BUG_10796

#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct RocqBug10796 {
  static inline const unsigned int a = 0u;
};

#endif // INCLUDED_ROCQ_BUG_10796
