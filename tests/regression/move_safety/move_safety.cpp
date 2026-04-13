#include <move_safety.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// TEST 2: Store partial application in a Box.
/// If the eta-expanded lambda uses & capture,
/// the Box will hold a dangling reference after the
/// function returns.
std::shared_ptr<MoveSafety::fn_box>
MoveSafety::make_box(std::shared_ptr<MoveSafety::tree> t) {
  return fn_box::box([=](unsigned int _x0) mutable -> unsigned int {
    return t->sum_values(_x0);
  });
}

/// TEST 4: Partial application followed by identity function
/// that takes by value (returns its argument).
std::shared_ptr<MoveSafety::tree>
MoveSafety::tree_id(std::shared_ptr<MoveSafety::tree> t) {
  return t;
}
