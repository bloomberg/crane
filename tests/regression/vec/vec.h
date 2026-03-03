#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Vec {
  static inline const persistent_array<int64_t> test1 =
      persistent_array<int64_t>(int64_t(5), int64_t(12));

  static inline const int64_t test2 = test1.length();

  static inline const int64_t test3 = test1.get(int64_t(3));

  static inline const persistent_array<int64_t> test4 =
      test1.set(int64_t(2), int64_t(14));
};
