// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <instance_op_coercion_position.h>

#include <iostream>

int main() {
  using M = InstanceOpCoercionPosition::M3_2;
  if (M::op(false, false) != false || M::op(false, true) != true ||
      M::op(true, false) != true) {
    std::cout << "FAIL: M3_2::op" << std::endl;
    return 1;
  }
  std::cout << "All instance_op_coercion_position tests passed!" << std::endl;
  return 0;
}
