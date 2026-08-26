#include <nested_fix_loopify.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = NestedFixLoopify::go(4);
  std::cout << "go 4 = " << r << " (want 24)" << std::endl;
  assert(r == 24);
  return 0;
}
