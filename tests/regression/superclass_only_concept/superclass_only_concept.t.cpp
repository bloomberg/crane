#include <superclass_only_concept.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = SuperclassOnlyConcept::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(6)) {
    std::cout << "expected " << UINT64_C(6) << std::endl;
    return 1;
  }
  return 0;
}
