#ifndef INCLUDED_CTOR_ESCAPE_COLLISION
#define INCLUDED_CTOR_ESCAPE_COLLISION

#include <cstdint>
#include <utility>

struct CtorEscapeCollision {
  enum class Item { D_, D_0, D_P, D_P0, D_P1, D_P2 };

  template <typename T1>
  static T1 item_rect(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, Item i) {
    switch (i) {
    case Item::D_: {
      return f;
    }
    case Item::D_0: {
      return f0;
    }
    case Item::D_P: {
      return f1;
    }
    case Item::D_P0: {
      return f2;
    }
    case Item::D_P1: {
      return f3;
    }
    case Item::D_P2: {
      return f4;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 item_rec(T1 f, T1 f0, T1 f1, T1 f2, T1 f3, T1 f4, Item i) {
    return item_rect<T1>(std::move(f), std::move(f0), std::move(f1),
                         std::move(f2), std::move(f3), std::move(f4), i);
  }

  static uint64_t tag(Item x);
  static inline const uint64_t t =
      (((((tag(Item::D_) + tag(Item::D_0)) + tag(Item::D_P)) +
         tag(Item::D_P0)) +
        tag(Item::D_P1)) +
       tag(Item::D_P2));
};

#endif // INCLUDED_CTOR_ESCAPE_COLLISION
