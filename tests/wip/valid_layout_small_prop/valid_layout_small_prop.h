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

struct ValidLayoutSmallProp {
  struct layout {
    unsigned int base_addr;
    unsigned int code_size;
  };

  static unsigned int base_addr(const std::shared_ptr<layout> &l);

  static unsigned int code_size(const std::shared_ptr<layout> &l);
};
