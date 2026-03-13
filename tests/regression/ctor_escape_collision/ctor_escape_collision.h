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
  enum class Item { e_D_, e_D_0, e_D__, e_D__0, e_D__1, e_D__2 };

  template <typename T1>
  static T1 item_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const T1 f4, const Item i) {
    return [&](void) {
      switch (i) {
      case Item::e_D_: {
        return f;
      }
      case Item::e_D_0: {
        return f0;
      }
      case Item::e_D__: {
        return f1;
      }
      case Item::e_D__0: {
        return f2;
      }
      case Item::e_D__1: {
        return f3;
      }
      case Item::e_D__2: {
        return f4;
      }
      }
    }();
  }

  template <typename T1>
  static T1 item_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                     const T1 f3, const T1 f4, const Item i) {
    return [&](void) {
      switch (i) {
      case Item::e_D_: {
        return f;
      }
      case Item::e_D_0: {
        return f0;
      }
      case Item::e_D__: {
        return f1;
      }
      case Item::e_D__0: {
        return f2;
      }
      case Item::e_D__1: {
        return f3;
      }
      case Item::e_D__2: {
        return f4;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int tag(const Item x);
  static inline const unsigned int t =
      (((((tag(Item::e_D_) + tag(Item::e_D_0)) + tag(Item::e_D__)) +
         tag(Item::e_D__0)) +
        tag(Item::e_D__1)) +
       tag(Item::e_D__2));
};

#endif // INCLUDED_CTOR_ESCAPE_COLLISION
