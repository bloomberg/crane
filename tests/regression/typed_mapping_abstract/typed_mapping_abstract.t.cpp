// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// An abstract typed-mapped type (std::int64_t) used through legacy inline
// constants.  The refused uses are checked while the .vo is built.
#include <typed_mapping_abstract.h>

#include <cstdint>
#include <iostream>
#include <type_traits>

using T = TypedMappingAbstract;

static_assert(std::is_same_v<decltype(&T::later), std::int64_t (*)(std::int64_t)>);

int main() {
  int failures = 0;
  if (T::count_to(5) != 5) {
    std::cout << "FAIL: count_to(5) is " << T::count_to(5) << "\n";
    ++failures;
  }
  if (T::later(40) != 42) {
    std::cout << "FAIL: later(40)\n";
    ++failures;
  }
  if (T::ticks(3, 10) != 13) {
    std::cout << "FAIL: ticks(3, 10)\n";
    ++failures;
  }
  if (failures == 0) {
    std::cout << "All typed_mapping_abstract tests passed!\n";
    return 0;
  }
  return 1;
}
