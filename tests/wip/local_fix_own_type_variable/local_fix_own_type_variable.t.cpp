#include <local_fix_own_type_variable.h>

#include <cstdint>
#include <iostream>

#define M LocalFixOwnTypeVariable

int main() {
  int fails = 0;
  if (!(M::t == 3)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }
  if (!(M::v == 4)) { std::cout << "FAIL: M::v" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All local_fix_own_type_variable tests passed!" << std::endl;
  return fails;
}
