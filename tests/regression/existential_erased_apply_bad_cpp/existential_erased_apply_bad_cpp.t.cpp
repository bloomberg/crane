#include "existential_erased_apply_bad_cpp.h"
#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // 5 + (5 + 6) + 3 = 19
  auto r = ExistentialErasedApplyBadCpp::run(UINT64_C(5));
  std::cout << "run(5) = " << r << std::endl;
  assert(r == 19);
  return 0;
}
