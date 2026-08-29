#include <dep_return_any_cast.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = DepReturnAnyCast::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(10)) {
    std::cout << "expected " << UINT64_C(10) << std::endl;
    return 1;
  }
  return 0;
}
