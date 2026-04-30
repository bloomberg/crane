#include <wrapper_collision_pos.h>

unsigned int WrapperCollisionPos::Left::Pos::id_left(const unsigned int n) {
  return n;
}

unsigned int WrapperCollisionPos::Right::Pos::inc_right(const unsigned int n) {
  return (n + 1);
}
