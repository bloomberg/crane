#ifndef INCLUDED_CLOCK
#define INCLUDED_CLOCK

#include <chrono>
#include <cstdint>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct Clock {
  static int64_t get_steady();
  static int64_t get_system();
  static int64_t get_time();
  static int64_t elapsed();
};

#endif // INCLUDED_CLOCK
