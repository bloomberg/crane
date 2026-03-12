#ifndef INCLUDED_CTOR_ESCAPE_COLLISION
#define INCLUDED_CTOR_ESCAPE_COLLISION

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

struct CtorEscapeCollision {
  enum class item { D_, D_0, D__, D__0, D__1, D__2 };

  template <typename T1>
  static T1 item_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const T1 f4, const item i) {
    return [&](void) {
      switch (i) {
      case item::D_: {
        return f;
      }
      case item::D_0: {
        return f0;
      }
      case item::D__: {
        return f1;
      }
      case item::D__0: {
        return f2;
      }
      case item::D__1: {
        return f3;
      }
      case item::D__2: {
        return f4;
      }
      }
    }();
  }

  template <typename T1>
  static T1 item_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                     const T1 f3, const T1 f4, const item i) {
    return [&](void) {
      switch (i) {
      case item::D_: {
        return f;
      }
      case item::D_0: {
        return f0;
      }
      case item::D__: {
        return f1;
      }
      case item::D__0: {
        return f2;
      }
      case item::D__1: {
        return f3;
      }
      case item::D__2: {
        return f4;
      }
      }
    }();
  }

  static unsigned int tag(const item x);
  static inline const unsigned int t =
      (((((tag(item::D_) + tag(item::D_0)) + tag(item::D__)) +
         tag(item::D__0)) +
        tag(item::D__1)) +
       tag(item::D__2));
};

#endif // INCLUDED_CTOR_ESCAPE_COLLISION
