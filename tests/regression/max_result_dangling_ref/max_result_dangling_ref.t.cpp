// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <max_result_dangling_ref.h>

#include <cstdint>
#include <iostream>

#define M MaxResultDanglingRef

int main() {
  int fails = 0;
  if (!(M::f(3, 9) == 10)) { std::cout << "FAIL: M::f(3, 9)" << std::endl; ++fails; }
  if (!(M::f(9, 3) == 9)) { std::cout << "FAIL: M::f(9, 3)" << std::endl; ++fails; }
  if (!(M::g(17, 5) == 2)) { std::cout << "FAIL: M::g(17, 5)" << std::endl; ++fails; }
  if (!(M::g(17, 0) == 0)) { std::cout << "FAIL: M::g(17, 0)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All max_result_dangling_ref tests passed!" << std::endl;
  return fails;
}
