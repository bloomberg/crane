#include <method_partial_app.h>

#include <cassert>
#include <iostream>

int main() {
  using MPA = MethodPartialApp;

  // method_partial_bug: f = add_to_sum t, called twice
  // std::move(t)->add_to_sum(x) uses operator-> which doesn't consume unique_ptr
  // Expected: (60 + 5) + (60 + 10) = 65 + 70 = 135
  auto r1 = MPA::method_partial_bug;
  std::cout << "method_partial_bug = " << r1 << std::endl;
  assert(r1 == 135u);

  // method_partial_box: partial app stored in box
  // Expected: (60 + 5) + (60 + 10) = 135
  auto r2 = MPA::method_partial_box;
  std::cout << "method_partial_box = " << r2 << std::endl;
  assert(r2 == 135u);

  // method_partial_two: two partial apps from different trees
  // Expected: (10 + 0) + (20 + 0) = 30
  auto r3 = MPA::method_partial_two;
  std::cout << "method_partial_two = " << r3 << std::endl;
  assert(r3 == 30u);

  std::cout << "All method_partial_app tests passed!" << std::endl;
  return 0;
}
