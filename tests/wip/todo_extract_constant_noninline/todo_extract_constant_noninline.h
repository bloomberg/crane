#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <todo_extract_constant_noninline_support.h>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct TodoExtractConstantNoninline {
  static unsigned int foreign_inc(const unsigned int);

  static inline const unsigned int test_value =
      foreign_inc(((((0 + 1) + 1) + 1) + 1));

  static inline const unsigned int twice_value =
      foreign_inc(foreign_inc(((0 + 1) + 1)));
};
