#ifndef INCLUDED_WRAPPER_COLLISION_POS
#define INCLUDED_WRAPPER_COLLISION_POS

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct WrapperCollisionPos {
  struct Left {
    struct Pos {
      static unsigned int id_left(unsigned int n);
    };
  };

  struct Right {
    struct Pos {
      static unsigned int inc_right(unsigned int n);
    };
  };

  static inline const unsigned int t1 = Left::Pos::id_left(1u);
  static inline const unsigned int t2 = Right::Pos::inc_right(1u);
};

#endif // INCLUDED_WRAPPER_COLLISION_POS
