#include <pos_sub_saturates.h>

#include <cstdint>
#include <iostream>

#define M PosSubSaturates

int main() {
  int fails = 0;
  if (!(M::s(2, 5) == 1)) { std::cout << "FAIL: M::s(2, 5)" << std::endl; ++fails; }
  if (!(M::s(5, 5) == 1)) { std::cout << "FAIL: M::s(5, 5)" << std::endl; ++fails; }
  if (!(M::s(5, 2) == 3)) { std::cout << "FAIL: M::s(5, 2)" << std::endl; ++fails; }
  if (!(M::p(1) == 1)) { std::cout << "FAIL: M::p(1)" << std::endl; ++fails; }
  if (!(M::p(4) == 3)) { std::cout << "FAIL: M::p(4)" << std::endl; ++fails; }
  if (!(M::t == 1)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All pos_sub_saturates tests passed!" << std::endl;
  return fails;
}
