#include <move_safety.h>

#include <cassert>
#include <iostream>

int main() {
  using MS = MoveSafety;

  // TEST 2: bug_box_escape — heap-use-after-free
  // make_box(t) stores a [&] lambda in a Box, capturing parameter t
  // by reference. When make_box returns, t is destroyed, and the
  // closure holds a dangling reference. Using the Box crashes.
  auto r2 = MS::bug_box_escape;
  std::cout << "bug_box_escape = " << r2 << std::endl;
  assert(r2 == 159u);

  // TEST 4: bug_partial_then_id — use-after-move
  // Same pattern as partial_app_move: [&] lambda captures t,
  // tree_id takes t by value, std::move(t) applied, lambda dangles.
  auto r4 = MS::bug_partial_then_id;
  std::cout << "bug_partial_then_id = " << r4 << std::endl;
  assert(r4 == 80u);

  std::cout << "All move_safety tests passed!" << std::endl;
  return 0;
}
