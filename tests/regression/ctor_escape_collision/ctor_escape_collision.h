#ifndef INCLUDED_CTOR_ESCAPE_COLLISION
#define INCLUDED_CTOR_ESCAPE_COLLISION

#include <utility>

struct CtorEscapeCollision {
  enum class Item { D_, D_0, D__, D__0, D__1, D__2 };

  template <typename T1>
  static T1 item_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, Item i) {
    switch (i) {
    case Item::D_: {
      return f;
    }
    case Item::D_0: {
      return f0;
    }
    case Item::D__: {
      return f1;
    }
    case Item::D__0: {
      return f2;
    }
    case Item::D__1: {
      return f3;
    }
    case Item::D__2: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 item_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, Item i) {
    switch (i) {
    case Item::D_: {
      return f;
    }
    case Item::D_0: {
      return f0;
    }
    case Item::D__: {
      return f1;
    }
    case Item::D__0: {
      return f2;
    }
    case Item::D__1: {
      return f3;
    }
    case Item::D__2: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  static unsigned int tag(Item x);
  static inline const unsigned int t =
      (((((tag(Item::D_) + tag(Item::D_0)) + tag(Item::D__)) +
         tag(Item::D__0)) +
        tag(Item::D__1)) +
       tag(Item::D__2));
};

#endif // INCLUDED_CTOR_ESCAPE_COLLISION
