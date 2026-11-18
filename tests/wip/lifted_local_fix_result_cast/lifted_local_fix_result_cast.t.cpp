#include <lifted_local_fix_result_cast.h>

#include <cstdint>
#include <iostream>

#define M LiftedLocalFixResultCast

int main() {
  int fails = 0;
  if (!(M::t == true)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All lifted_local_fix_result_cast tests passed!" << std::endl;
  return fails;
}
