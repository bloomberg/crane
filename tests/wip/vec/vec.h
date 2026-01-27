#include <algorithm>
#include <any>
#include <array>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Vec {
  static inline const std::array<int, int> test1 = []() -> std::array<int, 5> {
    std::array<int, 5> _arr;
    _arr.fill(12);
    return _arr;
  }();

  static inline const int test2 = test1.size();

  static inline const std::optional<int> test3 = []() -> std::optional<int> {
    if (3 < 5) {
      return std::make_optional<int>(test1[3]);
    } else {
      return std::nullopt;
    }
  }();

  static inline const std::array<int, int> test4 = []() -> std::array<int, 5> {
    std::array<int, 5> _arr = test1;
    if (2 < 5) {
      _arr[2] = 14;
    }
    return _arr;
  }();
};
