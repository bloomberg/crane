#include <wrapper_collision_pos.h>

#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
WrapperCollisionPos::Left::Pos::id_left(const unsigned int n) {
  return std::move(n);
}

__attribute__((pure)) unsigned int
WrapperCollisionPos::Right::Pos::inc_right(const unsigned int n) {
  return (std::move(n) + 1);
}
