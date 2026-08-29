#include <eta_closure_first_class.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = EtaClosureFirstClass::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(600)) {
    std::cout << "expected " << UINT64_C(600) << std::endl;
    return 1;
  }
  return 0;
}
