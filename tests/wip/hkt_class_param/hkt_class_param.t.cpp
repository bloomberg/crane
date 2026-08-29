#include <hkt_class_param.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = HktClassParam::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(3)) {
    std::cout << "expected " << UINT64_C(3) << std::endl;
    return 1;
  }
  return 0;
}
