#include "option_nested_recursion_bad_cpp.h"
#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // build(5) is a chain of 6 links, so depth is 6.
  auto r = OptionNestedRecursionBadCpp::run(UINT64_C(5));
  std::cout << "run(5) = " << r << std::endl;
  assert(r == 6);
  return 0;
}
