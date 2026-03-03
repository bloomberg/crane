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

struct IdentifierEscapeSwitch {
  static unsigned int id_from_param(const unsigned int switch0);

  static unsigned int add_one_from_param(const unsigned int switch0);

  static inline const unsigned int t =
      add_one_from_param(((((((0 + 1) + 1) + 1) + 1) + 1) + 1));
};
