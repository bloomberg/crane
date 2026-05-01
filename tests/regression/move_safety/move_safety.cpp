#include <move_safety.h>

/// TEST 2: Store partial application in a Box.
/// If the eta-expanded lambda uses & capture,
/// the Box will hold a dangling reference after the
/// function returns.
MoveSafety::fn_box MoveSafety::make_box(MoveSafety::tree t) {
  return fn_box::box([=](unsigned int _x0) mutable -> unsigned int {
    return t.sum_values(_x0);
  });
}
