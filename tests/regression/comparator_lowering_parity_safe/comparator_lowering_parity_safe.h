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

struct ComparatorLoweringParitySafe {
  struct A {
    struct CmpLeft {
      static unsigned int f(const unsigned int n);
    };
  };

  struct B {
    struct CmpRight {
      static unsigned int g(const unsigned int n);
    };
  };

  static inline const unsigned int t =
      (A::CmpLeft::f(0) + B::CmpRight::g((0 + 1)));
};
