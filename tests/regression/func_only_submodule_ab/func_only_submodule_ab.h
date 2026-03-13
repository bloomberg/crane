#ifndef INCLUDED_FUNC_ONLY_SUBMODULE_AB
#define INCLUDED_FUNC_ONLY_SUBMODULE_AB

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

struct FuncOnlySubmoduleAb {
  struct Root {
    struct A {
      __attribute__((pure)) static unsigned int inc(const unsigned int n);
    };

    struct B {
      __attribute__((pure)) static unsigned int dec(const unsigned int _x0);
    };
  };

  static inline const unsigned int t = Root::A::inc(Root::B::dec(3u));
};

#endif // INCLUDED_FUNC_ONLY_SUBMODULE_AB
