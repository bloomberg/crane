// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <boxed_fields.h>

#include <cstdint>
#include <iostream>
#include <variant>

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

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using BF = BoxedFields;

int main() {
  ASSERT(BF::sample_total == 36);
  ASSERT(BF::moved_total == 76);

  // A boxed field, as a structured binding sees it: the pointer.
  const auto &[sh, rest] = std::get<BF::scene::Layer>(BF::sample.v());
  const auto &[center, r] = std::get<BF::shape::Circle>(sh->v());
  ASSERT(r == 3);
  ASSERT(center->px() == 1 && center->py() == 2);

  // Copying a value shares its boxed fields.
  BF::scene copy = BF::sample;
  const auto &[sh2, rest2] = std::get<BF::scene::Layer>(copy.v());
  ASSERT(sh2.get() == sh.get());
  ASSERT(copy.total() == 36);

  // A parameter field: boxed when it holds a scene, held inline as a number.
  ASSERT(BF::heavy_total == 37);
  ASSERT(BF::light_total == 42);
  static_assert(!crane::copy_is_cheap<BF::scene>::value);
  static_assert(crane::copy_is_cheap<uint64_t>::value);

  if (testStatus == 0) {
    std::cout << "All boxed_fields tests passed!" << std::endl;
  }
  return testStatus;
}
