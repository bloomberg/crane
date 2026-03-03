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

struct WrapperDeclMerge {
  struct A {
    struct Nat {
      static unsigned int fa(const unsigned int n);
    };
  };

  struct B {
    struct Nat {
      static unsigned int fb(const unsigned int n);
    };
  };

  static inline const unsigned int x = A::Nat::fa(((((0 + 1) + 1) + 1) + 1));

  static inline const unsigned int y = B::Nat::fb(((((0 + 1) + 1) + 1) + 1));
};
