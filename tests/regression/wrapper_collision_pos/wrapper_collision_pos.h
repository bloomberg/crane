#ifndef INCLUDED_WRAPPER_COLLISION_POS
#define INCLUDED_WRAPPER_COLLISION_POS

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

struct WrapperCollisionPos {
  struct Left {
    struct Pos {
      __attribute__((pure)) static unsigned int id_left(const unsigned int n);
    };
  };

  struct Right {
    struct Pos {
      __attribute__((pure)) static unsigned int inc_right(const unsigned int n);
    };
  };

  static inline const unsigned int t1 = Left::Pos::id_left(1u);
  static inline const unsigned int t2 = Right::Pos::inc_right(1u);
};

#endif // INCLUDED_WRAPPER_COLLISION_POS
