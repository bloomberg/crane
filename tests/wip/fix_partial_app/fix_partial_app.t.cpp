#include <fix_partial_app.h>

#include <cassert>
#include <iostream>

int main() {
  using FPA = FixPartialApp;

  // fix_partial_bug: f = count_nodes tree, called twice
  // BUG: [&] capture with std::move(t) that converts unique_ptr to shared_ptr.
  // First call consumes the unique_ptr, second call passes null → CRASH
  // Expected: count_nodes(tree, 0) + count_nodes(tree, 100) = 3 + 103 = 106
  auto r1 = FPA::fix_partial_bug;
  std::cout << "fix_partial_bug = " << r1 << std::endl;
  assert(r1 == 106u);

  // fix_partial_pair: same through pair
  auto r2 = FPA::fix_partial_pair;
  std::cout << "fix_partial_pair = " << r2 << std::endl;
  assert(r2 == 106u);

  // map_partial_bug: partial app of tree_map with stateless lambda
  // No capture issues. Expected: (11) + (21) = 32
  auto r3 = FPA::map_partial_bug;
  std::cout << "map_partial_bug = " << r3 << std::endl;
  assert(r3 == 32u);

  std::cout << "All fix_partial_app tests passed!" << std::endl;
  return 0;
}
