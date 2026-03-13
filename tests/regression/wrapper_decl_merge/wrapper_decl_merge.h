#ifndef INCLUDED_WRAPPER_DECL_MERGE
#define INCLUDED_WRAPPER_DECL_MERGE

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
      __attribute__((pure)) static unsigned int fa(const unsigned int n);
    };
  };

  struct B {
    struct Nat {
      __attribute__((pure)) static unsigned int fb(const unsigned int n);
    };
  };

  static inline const unsigned int x = A::Nat::fa(4u);
  static inline const unsigned int y = B::Nat::fb(4u);
};

#endif // INCLUDED_WRAPPER_DECL_MERGE
