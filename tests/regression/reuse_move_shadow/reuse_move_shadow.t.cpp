#include <reuse_move_shadow.h>

#include <cassert>
#include <iostream>

int main() {
  using RMS = ReuseMoveShadow;

  auto r1 = RMS::test1;
  std::cout << "test1 = " << r1 << " (expected 12)" << std::endl;
  assert(r1 == 12u);

  auto r2 = RMS::test2;
  std::cout << "test2 = " << r2 << " (expected 19)" << std::endl;
  assert(r2 == 19u);

  auto r3 = RMS::test3;
  std::cout << "test3 = " << r3 << " (expected 47)" << std::endl;
  assert(r3 == 47u);

  std::cout << "All tests passed!" << std::endl;
  return 0;
}
