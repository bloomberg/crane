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

struct NestedRecordUpdateQual {
  struct Shadow {
    unsigned int value;
  };

  static std::shared_ptr<Shadow> bump(const std::shared_ptr<Shadow> &x);

  static inline const std::shared_ptr<Shadow> t =
      bump(std::make_shared<Shadow>(Shadow{(0 + 1)}));
};
