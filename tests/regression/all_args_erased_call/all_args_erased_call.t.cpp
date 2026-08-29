#include <all_args_erased_call.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = AllArgsErasedCall::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(7)) {
    std::cout << "expected " << UINT64_C(7) << std::endl;
    return 1;
  }
  return 0;
}
