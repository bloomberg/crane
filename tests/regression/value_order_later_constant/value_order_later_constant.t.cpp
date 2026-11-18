// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <value_order_later_constant.h>

#include <iostream>

#define M ValueOrderLaterConstant

int main() {
  int fails = 0;
  if (!(M::t_1 == 1)) { std::cout << "FAIL: M::t_1" << std::endl; ++fails; }
  if (!(M::f4 == 0)) { std::cout << "FAIL: M::f4" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All value_order_later_constant tests passed!" << std::endl;
  return fails;
}
