#ifndef INCLUDED_PRIM_ARRAY_OPS
#define INCLUDED_PRIM_ARRAY_OPS

#include <cstdint>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PrimArrayOps {
  static inline const persistent_array<int64_t> test1 =
      persistent_array<int64_t>(int64_t(5), int64_t(12));
  static inline const int64_t test2 = test1.length();
  static inline const int64_t test3 = test1.get(int64_t(3));
  static inline const persistent_array<int64_t> test4 =
      test1.set(int64_t(2), int64_t(14));
};

#endif // INCLUDED_PRIM_ARRAY_OPS
