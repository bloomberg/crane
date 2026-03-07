#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RegPairOddProjection {
  static unsigned int pair_base(const unsigned int r);

  static inline const bool t =
      (pair_base((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1)) ==
       ((((((0 + 1) + 1) + 1) + 1) + 1) + 1));
};
