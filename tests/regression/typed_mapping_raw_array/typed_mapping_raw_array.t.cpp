// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "typed_mapping_raw_array.h"

#include <iostream>
#include <type_traits>
#include <vector>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

using T = TypedMappingRawArray;
using NatArray = std::vector<uint64_t> *;

// Read and write take the pointer by value; replace takes it by reference.
static_assert(
    std::is_same_v<decltype(&T::get_cell), uint64_t (*)(NatArray, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::set_cell),
                             NatArray (*)(NatArray, uint64_t, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::set_middle),
                             NatArray (*)(NatArray, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::set_outer), uint64_t (*)(NatArray)>);
static_assert(std::is_same_v<decltype(&T::reseat_cell),
                             uint64_t (*)(NatArray &, uint64_t)>);
static_assert(std::is_same_v<decltype(&T::flip_cell),
                             bool (*)(std::vector<bool> *, uint64_t)>);

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  {
    auto [w, r] = T::run_nat(3);
    ASSERT(w == 2);
    ASSERT(r == 0);
    std::cout << "run_nat 3: (" << w << ", " << r << ")" << std::endl;
  }
  {
    ASSERT(T::run_bool(2));
    std::cout << "run_bool 2: ok" << std::endl;
  }
  {
    NatArray a = raw_support::make<uint64_t>(3, 4);
    NatArray before = a;
    ASSERT(T::set_outer(a) == 2);
    ASSERT(a == before && (*a)[1] == 2);
    ASSERT(T::reseat_cell(a, 6) == 4);
    ASSERT(a != before && a->size() == 6);
    std::cout << "reseat: ok" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll typed_mapping_raw_array tests passed!" << std::endl;
  }
  return testStatus;
}
