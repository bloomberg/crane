#include "move_safety.h"

MoveSafety::fn_box MoveSafety::make_box(MoveSafety::tree t) {
  return fn_box::box(
      [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); });
}
