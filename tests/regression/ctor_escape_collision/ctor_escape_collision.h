#ifndef INCLUDED_CTOR_ESCAPE_COLLISION
#define INCLUDED_CTOR_ESCAPE_COLLISION

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

struct CtorEscapeCollision {
  enum class Item { e_D_, e_D_0, e_D__, e_D__0, e_D__1, e_D__2 };

  template <typename T1>
  static T1 item_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, const Item i) {
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
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 item_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, const Item i) {
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
    default:
      std::unreachable();
    }
  }

  static unsigned int tag(const Item x);
  static inline const unsigned int t =
      (((((tag(Item::e_D_) + tag(Item::e_D_0)) + tag(Item::e_D__)) +
         tag(Item::e_D__0)) +
        tag(Item::e_D__1)) +
       tag(Item::e_D__2));
};

#endif // INCLUDED_CTOR_ESCAPE_COLLISION
