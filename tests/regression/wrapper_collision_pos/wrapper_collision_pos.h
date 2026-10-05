#ifndef INCLUDED_WRAPPER_COLLISION_POS
#define INCLUDED_WRAPPER_COLLISION_POS

#include <cstdint>

struct WrapperCollisionPos {
  struct Left {
    struct Pos {
      static uint64_t id_left(uint64_t n);
    };
  };

  struct Right {
    struct Pos {
      static uint64_t inc_right(uint64_t n);
    };
  };

  static constexpr uint64_t t1 = UINT64_C(1);
  static constexpr uint64_t t2 = UINT64_C(2);
};

#endif // INCLUDED_WRAPPER_COLLISION_POS
