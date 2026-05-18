#ifndef INCLUDED_WRAPPER_COLLISION_POS
#define INCLUDED_WRAPPER_COLLISION_POS

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

  static inline const uint64_t t1 = Left::Pos::id_left(UINT64_C(1));
  static inline const uint64_t t2 = Right::Pos::inc_right(UINT64_C(1));
};

#endif // INCLUDED_WRAPPER_COLLISION_POS
