#include <fix_escape_capture.h>

#include <cassert>
#include <iostream>

int main() {
  using FEC = FixEscapeCapture;

  // test_pair: make_pair_fn(5) returns (5, add).
  // add(3) should return 5+3 = 8.
  // BUG: add captures base by [&]; after make_pair_fn returns,
  // base is destroyed → use-after-free when add is invoked.
  auto r1 = FEC::test_pair;
  std::cout << "test_pair = " << r1 << std::endl;
  assert(r1 == 8u);

  // test_pair2: make_pair_fn2(5) returns (id_add(5), id_add).
  // id_add(5) = 5+5 = 10, id_add(3) = 5+3 = 8, total = 18.
  auto r2 = FEC::test_pair2;
  std::cout << "test_pair2 = " << r2 << std::endl;
  assert(r2 == 18u);

  std::cout << "All fix_escape_capture tests passed!" << std::endl;
  return 0;
}
