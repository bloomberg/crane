#include <assoc_type_two_swapped.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = AssocTypeTwoSwapped::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(12)) {
    std::cout << "expected " << UINT64_C(12) << std::endl;
    return 1;
  }
  return 0;
}
