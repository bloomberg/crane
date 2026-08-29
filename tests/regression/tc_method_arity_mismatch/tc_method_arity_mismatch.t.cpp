#include <tc_method_arity_mismatch.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = TcMethodArityMismatch::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(5)) {
    std::cout << "expected " << UINT64_C(5) << std::endl;
    return 1;
  }
  return 0;
}
