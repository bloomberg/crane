#include "recursive_record_incomplete_type.h"
#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // kids sum to 5+6+7 = 18; a = 1+18 = 19, b = 2+18 = 20, total 39.
  auto r = RecursiveRecordIncompleteType::run(UINT64_C(5));
  std::cout << "run(5) = " << r << std::endl;
  assert(r == 39);
  return 0;
}
