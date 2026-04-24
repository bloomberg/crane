#include <wrapper_collision_pos.h>

#include <type_traits>

__attribute__((pure)) unsigned int
WrapperCollisionPos::Left::Pos::id_left(unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
WrapperCollisionPos::Right::Pos::inc_right(unsigned int n) {
  return (n + 1);
}
