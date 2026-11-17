#include <partial_app_prefix_work.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // g x = (x + 3) * 2 + 1, the composition of fs3; mk2's is
  // (x + 6) * 4 + 2; shifted's is g (x + 5).  run 10 sums, for i < 10,
  // g, mkp's g, mk2's, shifted's and g again, then g once more over map.
  auto r = PartialAppPrefixWork::run(UINT64_C(10));
  std::cout << "run(10) = " << r << std::endl;
  assert(r == 1340);
  return 0;
}
