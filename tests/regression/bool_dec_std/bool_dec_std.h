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

struct Bool {
  static bool bool_dec(const bool b1, const bool b2);
};

struct BoolDecStd {
  static bool eqb_dec(const bool a, const bool b);

  static inline const bool t1 = eqb_dec(true, true);

  static inline const bool t2 = eqb_dec(true, false);
};
