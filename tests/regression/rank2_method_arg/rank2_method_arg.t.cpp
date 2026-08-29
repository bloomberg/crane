#include <rank2_method_arg.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = Rank2MethodArg::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(4)) {
    std::cout << "expected " << UINT64_C(4) << std::endl;
    return 1;
  }
  return 0;
}
