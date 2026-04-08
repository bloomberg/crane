#include <map_partial_app.h>

#include <cassert>
#include <iostream>

int main() {
  using MPA = MapPartialApp;

  // map_partial_bug: partial app (wrap t) is called 3 times via list map.
  // BUG: std::move(t) inside [&] lambda body — first call moves unique_ptr t,
  // subsequent calls pass null shared_ptr → Node with null child → null deref.
  // Expected: sum_list [11; 12; 13] = 36
  auto r1 = MPA::map_partial_bug;
  std::cout << "map_partial_bug = " << r1 << std::endl;
  assert(r1 == 36u);

  // map_partial_pair: same but with pair indirection
  auto r2 = MPA::map_partial_pair;
  std::cout << "map_partial_pair = " << r2 << std::endl;
  assert(r2 == 36u);

  // map_two_closures: two different closures mapped over two lists
  // Expected: sum_list [11; 12] + sum_list [23; 24] = 23 + 47 = 70
  auto r3 = MPA::map_two_closures;
  std::cout << "map_two_closures = " << r3 << std::endl;
  assert(r3 == 70u);

  std::cout << "All map_partial_app tests passed!" << std::endl;
  return 0;
}
