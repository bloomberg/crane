#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct NatSubUnderflowSafe {
  static unsigned int sub_checked(const unsigned int, const unsigned int);

  static unsigned int sub_alt(const unsigned int a, const unsigned int b);

  static inline const unsigned int t =
      (sub_checked((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                   (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)) +
       sub_alt((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
               (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1)));
};
