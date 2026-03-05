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

struct NestedRecordUpdateQualSafe {
  struct cell {
    unsigned int value;
  };

  static std::shared_ptr<cell> bump(const std::shared_ptr<cell> &x);

  static unsigned int project(const std::shared_ptr<cell> &x);

  static inline const unsigned int t =
      project(bump(std::make_shared<cell>(cell{(0 + 1)})));
};
