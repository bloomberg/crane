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

struct FuncOnlySubmodulePair {
  struct Outer {
    struct A {
      static unsigned int inc(const unsigned int n);
    };

    struct B {
      static unsigned int dec(const unsigned int);
    };
  };

  static inline const unsigned int t =
      Outer::A::inc(Outer::B::dec((((0 + 1) + 1) + 1)));
};
