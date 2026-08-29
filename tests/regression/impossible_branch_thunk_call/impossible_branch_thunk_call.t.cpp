#include <impossible_branch_thunk_call.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = ImpossibleBranchThunkCall::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(5)) {
    std::cout << "expected " << UINT64_C(5) << std::endl;
    return 1;
  }
  return 0;
}
