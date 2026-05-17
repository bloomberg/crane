#include "wrapper_collision_pos.h"

uint64_t WrapperCollisionPos::Left::Pos::id_left(uint64_t n) { return n; }

uint64_t WrapperCollisionPos::Right::Pos::inc_right(uint64_t n) {
  return (n + 1);
}
