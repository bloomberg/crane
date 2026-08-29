#include <list_app_stack_overflow.h>

#include <cstdint>
#include <iostream>

int main() {
  std::uint64_t got = ListAppStackOverflow::run(0);
  std::cout << "run(0) = " << got << std::endl;
  if (got != UINT64_C(19999900006)) {
    std::cout << "expected " << UINT64_C(19999900006) << std::endl;
    return 1;
  }
  return 0;
}
