#include <list_fold_left_stack_overflow.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = ListFoldLeftStackOverflow::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(19999900000)) {
    std::cout << "expected " << UINT64_C(19999900000) << std::endl;
    return 1;
  }
  return 0;
}
