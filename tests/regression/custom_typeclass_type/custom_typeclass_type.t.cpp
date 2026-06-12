// Regression test: typeclass Type-valued field with custom extraction.
// With the bug, this fails to compile (std::any vs uint64_t mismatch).

#include "custom_typeclass_type.h"

#include <iostream>

int main() {
  uint64_t result = test_new();
  if (result != 5) {
    std::cerr << "FAIL: test_new() = " << result << ", expected 5\n";
    return 1;
  }
  std::cout << "PASS: test_new() = " << result << "\n";
  return 0;
}
